import Leader.L4.ShortSelectorParity
import Leader.L4.ShortPacketTag
import Leader.L4.BStarShort
import Leader.L4.ShortResetFlow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow

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

open L4.MISByteRows (Link)

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


private def linkStep (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (ab : Pair (Patch 96)) (l : Link) : Pair (Patch 96) :=
  let (a,b) := ab
  let fu := oldK hu u
  let fv := oldK hv v
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

private def rowPrefix (headers : Pair Bool) (old : Pair (BitVec 96)) :
    (Fin 3 → Bool) × Pair (Patch 96) :=
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
  (win,(a,b))

private def rowPost (hv : Bool) (v : BitVec 96) (routed : Pair (Patch 96)) : Pair (Patch 96) :=
  if hv then
    let (p,t) := source v (oldK hv v 0)
    (routed.1,(routed.2.compose p).compose (match t with | none=>.empty _ | some t=>putK 0 t))
  else routed


def localRow (headers : Pair Bool) (old : Pair (BitVec 96)) : Pair (Patch 96) :=
  let (win,p) := rowPrefix headers old
  rowPost headers.2 old.2 ((links headers.2).foldl (linkStep headers.1 headers.2 old.1 old.2 win) p)

theorem localRow_eq (h : Pair Bool) (x : Pair (BitVec 96)) :
    localRow h x=MISByteRows.row h x := rfl


private theorem compose_empty {w : Nat} (p : Patch w) :
    p.compose (.empty w)=p := by
  cases p with
  | mk m v =>
    change Patch.mk (m ||| 0) (v &&& ~~~(0 : BitVec w) ||| 0 &&& 0)=Patch.mk m v
    simp

theorem link_reset_out (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (a b : Patch 96) (j k : Fin 3) (r : oldK hu u j=resetForward) :
    linkStep hu hv u v win (a,b) ⟨j,some k⟩ =
      ((a.compose (if hu && j==1 then putSeal none else .empty _)).compose (putK j T),
        b.compose (putK k resetForward)) := by
  unfold linkStep
  simp only [r]
  cases hu <;> by_cases J : j=1 <;>
    simp [ready,parked,resetForward,effect,arrival,J,compose_empty]

theorem link_reset_turn (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (a b : Patch 96) (j : Fin 3) (r : oldK hu u j=resetForward) :
    linkStep hu hv u v win (a,b) ⟨j,none⟩ =
      ((a.compose (if hu && j==1 then putSeal none else .empty _)).compose (putK j resetReply),b) := by
  unfold linkStep
  simp only [r]
  cases hu <;> by_cases J : j=1 <;>
    simp [ready,parked,resetForward,resetReply,effect,terminal,J,compose_empty]

theorem link_reset_back (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (a b : Patch 96) (j k : Fin 3) (trail : oldK hu u j=T)
    (r : oldK hv v k=resetReply) :
    linkStep hu hv u v win (a,b) ⟨j,some k⟩ =
      (a.compose (putK j resetReply),b.compose (putK k E)) := by
  simp [linkStep,r,trail,ready,T,resetReply]

theorem link_trail_guard (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (a b : Patch 96) (j k : Fin 3) (trail : oldK hu u j=T)
    (r : oldK hv v k=resetForward ∨ oldK hv v k=T) :
    linkStep hu hv u v win (a,b) ⟨j,some k⟩ = (a,b) := by
  rcases r with R | R <;> simp [linkStep,R,trail,ready,T,resetForward]

#print axioms localRow_eq
#print axioms link_reset_out
#print axioms link_reset_turn
#print axioms link_reset_back
#print axioms link_trail_guard

private def Frames (j : Fin 3) (p : Patch 96) : Prop :=
  ∀ x, (kField j).read (p.apply x)=(kField j).read x

private theorem empty_frames (j : Fin 3) : Frames j (.empty _) := by
  intro x
  congr 1
  change x &&& ~~~(0 : BitVec 96) ||| (0 &&& 0)=x
  change x &&& BitVec.allOnes 96 ||| 0 = x
  rw [BitVec.and_allOnes]
  exact BitVec.or_zero

private theorem compose_frames {j : Fin 3} {p q : Patch 96}
    (h : Frames j p) (k : Frames j q) : Frames j (p.compose q) := by
  intro x; rw [Patch.compose_apply,k,h]

private theorem keep_high {j : Fin 3} {o w : Nat} (ho : 57≤o)
    (f : o+w≤96) (v : Nat) : Frames j (put o w f v) := fun x=>read_put_high j ho f v x

private theorem effect_frames (j : Fin 3) (u v : BitVec 96) (hu hv : Bool)
    (l : Link) (win : Bool) (t : Token) :
    Frames j (effect u v hu hv l.src l.dst win t).1 ∧
      Frames j (effect u v hu hv l.src l.dst win t).2.1 := by
  unfold effect
  dsimp only
  split
  · exact ⟨empty_frames _,empty_frames _⟩
  split
  · split
    · exact ⟨empty_frames _,compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)⟩
    · exact ⟨empty_frames _,empty_frames _⟩
  split
  · exact ⟨empty_frames _,empty_frames _⟩
  split
  · exact ⟨keep_high (by decide) _ _,empty_frames _⟩
  split
  · exact ⟨empty_frames _,empty_frames _⟩
  split
  · split
    · exact ⟨empty_frames _,empty_frames _⟩
    · split
      · exact ⟨keep_high (by omega) _ _,empty_frames _⟩
      · exact ⟨keep_high (by decide) _ _,empty_frames _⟩
  · exact ⟨empty_frames _,empty_frames _⟩

private theorem link_left_frame (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (a b : Patch 96) (j : Fin 3) (l : Link) (neq : j≠l.src) (x : BitVec 96) :
    (kField j).read ((linkStep hu hv u v win (a,b) l).1.apply x)=
      (kField j).read (a.apply x) := by
  have Ef := (effect_frames j u v hu hv l (win l.src) (oldK hu u l.src)).1
  unfold linkStep
  dsimp only
  split
  · split <;> rw [Patch.compose_apply,read_putK_other _ _ neq,Patch.compose_apply,Ef]
  · split
    · rfl
    · split
      · split
        · rw [Patch.compose_apply,read_putK_other _ _ neq]
        · rfl
      · split
        · rw [Patch.compose_apply,read_putK_other _ _ neq]
        · split
          · rw [Patch.compose_apply,read_putK_other _ _ neq]
          · rfl

private theorem link_right_frame (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (a b : Patch 96) (j : Fin 3) (l : Link) (neq : some j≠l.dst) (x : BitVec 96) :
    (kField j).read ((linkStep hu hv u v win (a,b) l).2.apply x)=
      (kField j).read (b.apply x) := by
  have Ef := (effect_frames j u v hu hv l (win l.src) (oldK hu u l.src)).2
  unfold linkStep
  dsimp only
  split
  · split
    · rw [Patch.compose_apply,Ef]
    · rename_i k hk
      have ne : j≠k := fun e=>neq (congrArg some e |>.trans hk.symm)
      rw [Patch.compose_apply,read_putK_other _ _ ne,Patch.compose_apply,Ef]
  · split
    · rfl
    · split
      · rfl
      · rename_i k hk
        have ne : j≠k := fun e=>neq (congrArg some e |>.trans hk.symm)
        split
        · rw [Patch.compose_apply,read_putK_other _ _ ne]
        · split <;> rfl

#print axioms link_left_frame
#print axioms link_right_frame

private theorem source_hi (j : Fin 3) (v : BitVec 96) (t : Token) :
    Frames j (source v t).1 := by
  unfold source
  dsimp only
  split
  · exact keep_high (by decide) _ _
  split
  · refine compose_frames ?_ (keep_high (by decide) _ _)
    split
    · exact keep_high (by decide) _ _
    · exact empty_frames _
  split
  · exact empty_frames _
  split
  · exact keep_high (by decide) _ _
  split
  · exact keep_high (by decide) _ _
  · exact keep_high (by decide) _ _
  · split <;> exact keep_high (by decide) _ _
  · exact compose_frames (compose_frames (keep_high (by decide) _ _) (keep_high (by decide) _ _))
      (keep_high (by decide) _ _)
  · exact keep_high (by decide) _ _
  · exact keep_high (by decide) _ _
  · exact keep_high (by decide) _ _

private theorem post_frame (hv : Bool) (v : BitVec 96) (p : Pair (Patch 96)) (j : Fin 3)
    (healthy : hv=false ∨ j≠0 ∨ (source v (oldK hv v 0)).2=none) :
    (kField j).read ((rowPost hv v p).2.apply v)=(kField j).read (p.2.apply v) := by
  cases hv
  · rfl
  · have Hj := healthy.resolve_left (by decide)
    change (kField j).read (((p.2.compose (source v (oldK true v 0)).1).compose
        (match (source v (oldK true v 0)).2 with
        | none => Patch.empty 96 | some t => putK 0 t)).apply v)=_
    rw [Patch.compose_apply,Patch.compose_apply]
    cases E : (source v (oldK true v 0)).2 with
    | none => exact (empty_frames j _).trans (source_hi j v _ _)
    | some t =>
      have ne := Hj.resolve_right (by simp [E])
      change (kField j).read
        ((putK 0 t).apply ((source v (oldK true v 0)).1.apply (p.2.apply v)))=_
      rw [read_putK_other _ _ ne]
      exact source_hi j v _ _

private theorem fold_left_frame (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (p : Pair (Patch 96)) (j : Fin 3) (ls : List Link) (x : BitVec 96)
    (ne : ∀ l∈ls,j≠l.src) :
    (kField j).read ((ls.foldl (linkStep hu hv u v win) p).1.apply x)=
      (kField j).read (p.1.apply x) := by
  induction ls generalizing p with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldl_cons,ih _ (fun z hz=>ne z (List.mem_cons_of_mem _ hz))]
    rcases p with ⟨a,b⟩
    exact link_left_frame hu hv u v win a b j l (ne l (by simp)) x

private theorem fold_right_frame (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (p : Pair (Patch 96)) (j : Fin 3) (ls : List Link) (x : BitVec 96)
    (ne : ∀ l∈ls,some j≠l.dst) :
    (kField j).read ((ls.foldl (linkStep hu hv u v win) p).2.apply x)=
      (kField j).read (p.2.apply x) := by
  induction ls generalizing p with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldl_cons,ih _ (fun z hz=>ne z (List.mem_cons_of_mem _ hz))]
    rcases p with ⟨a,b⟩
    exact link_right_frame hu hv u v win a b j l (ne l (by simp)) x

/-- Immutable-old successor slot for each initiating occurrence. -/
def destination (hv : Bool) (j : Fin 3) : Option (Fin 3) :=
  if hv then if h : j.val+1<3 then some ⟨j.val+1,h⟩ else none else some j

private theorem link_split (hv : Bool) (j : Fin 3) :
    ∃ pre suf, links hv=pre++⟨j,destination hv j⟩::suf ∧
      (∀ l∈suf,j≠l.src) ∧
      (∀ k, destination hv j=some k → ∀ l∈suf, some k≠l.dst) := by
  obtain ⟨val,hj⟩ := j
  have V : val=0 ∨ val=1 ∨ val=2 := by omega
  rcases V with V|V|V <;> subst val <;> cases hv
  · refine ⟨[],[⟨1,some 1⟩,⟨2,some 2⟩],rfl,?_,?_⟩
    · intro l h; simp at h; rcases h with r|r <;> subst l <;> decide +revert
    · intro k hk l hl; cases hk; simp at hl; rcases hl with r|r <;> subst l <;> decide +revert
  · refine ⟨[],[⟨1,some 2⟩,⟨2,none⟩],rfl,?_,?_⟩
    · intro l h; simp at h; rcases h with r|r <;> subst l <;> decide +revert
    · intro k hk l hl; cases hk; simp at hl; rcases hl with r|r <;> subst l <;> decide +revert
  · refine ⟨[⟨0,some 0⟩],[⟨2,some 2⟩],rfl,?_,?_⟩
    · intro l h; simp at h; subst l; decide +revert
    · intro k hk l hl; cases hk; simp at hl; subst l; decide +revert
  · refine ⟨[⟨0,some 1⟩],[⟨2,none⟩],rfl,?_,?_⟩
    · intro l h; simp at h; subst l; decide +revert
    · intro k hk l hl; cases hk; simp at hl; subst l; decide +revert
  · refine ⟨[⟨0,some 0⟩,⟨1,some 1⟩],[],rfl,?_,?_⟩ <;> simp
  · refine ⟨[⟨0,some 1⟩,⟨1,some 2⟩],[],rfl,?_,?_⟩ <;> simp

private theorem header_destination_ne_zero (j k : Fin 3)
    (hk : destination true j=some k) : k≠0 := by
  change (if h : j.val+1<3 then some ⟨j.val+1,h⟩ else none)=some k at hk
  split at hk
  · intro Z
    subst k
    have V := congrArg Fin.val (Option.some.inj hk)
    change j.val+1=0 at V; omega
  · contradiction

private theorem rowPost_left (hv : Bool) (v : BitVec 96) (q : Pair (Patch 96)) :
    (rowPost hv v q).1=q.1 := by
  cases hv <;> rfl

/-- Actual complete MIS work pair: the selected authentic RESET advances
even across arbitrary destination bytes; unrelated fold iterations and a
simultaneous responder door action cannot rewrite either target K lane. -/
theorem reset_out_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (front : oldK hu u j=resetForward) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode T ∧
      (kField k).read (q.2.apply v)=encode resetForward := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k dst)
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,E⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change
    (kField j).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).1.apply u)=_ ∧
    (kField k).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).2.apply v)=_
  rw [E,dst,link_reset_out _ _ _ _ _ _ _ _ _ front]
  constructor
  · rw [rowPost_left,fold_left_frame _ _ _ _ _ _ _ _ _ A,Patch.compose_apply,read_putK]
  · rw [post_frame _ _ _ _ (post.imp_right .inl),fold_right_frame _ _ _ _ _ _ _ _ _ (Z k dst),
      Patch.compose_apply,read_putK]

#print axioms reset_out_pair

/-- Terminal RESET reverses at the actual complete pair, not just its link. -/
theorem reset_turn_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (dst : destination hv j=none) (front : oldK hu u j=resetForward) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode resetReply := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,E⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField j).read
    ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  rw [E,dst,link_reset_turn _ _ _ _ _ _ _ _ front,
    fold_left_frame _ _ _ _ _ _ _ _ _ A,Patch.compose_apply,read_putK]

/-- A returning RESET advances into its preceding actual trail, clearing its old slot. -/
theorem reset_back_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (back : oldK hv v k=resetReply) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode resetReply ∧
      (kField k).read (q.2.apply v)=encode E := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k dst)
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,E'⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change
    (kField j).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).1.apply u)=_ ∧
    (kField k).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).2.apply v)=_
  rw [E',dst,link_reset_back _ _ _ _ _ _ _ _ _ trail back]
  constructor
  · rw [rowPost_left,fold_left_frame _ _ _ _ _ _ _ _ _ A,Patch.compose_apply,read_putK]
  · rw [post_frame _ _ _ _ (post.imp_right .inl),fold_right_frame _ _ _ _ _ _ _ _ _ (Z k dst),
      Patch.compose_apply,read_putK]

#print axioms reset_turn_pair
#print axioms reset_back_pair
/-- RESET0 issue at a literal responder header overrides the complete route fold. -/
theorem reset_issue_pair (hu : Bool) (u v : BitVec 96)
    (phase : get v 81 2 (by decide)=1) (op : get v 78 3 (by decide)=0) :
    let q := MISByteRows.row (hu,true) (u,v)
    (kField 0).read (q.2.apply v)=encode resetForward := by
  rw [←localRow_eq]
  unfold localRow rowPost
  dsimp only
  rw [reset_issue_source v _ phase op]
  simp only [if_true,Patch.compose_apply,read_putK]

/-- RESET0 receipt at a literal responder header clears the root token. -/
theorem reset_consume_pair (hu : Bool) (u v : BitVec 96)
    (phase : get v 81 2 (by decide)=2) (op : get v 78 3 (by decide)=0)
    (reply : oldK true v 0=resetReply) :
    let q := MISByteRows.row (hu,true) (u,v)
    (kField 0).read (q.2.apply v)=encode E := by
  rw [←localRow_eq]
  unfold localRow rowPost
  dsimp only
  rw [reply,reset_consume_source v phase op]
  simp only [if_true,Patch.compose_apply,read_putK]

#print axioms reset_issue_pair
#print axioms reset_consume_pair
private theorem links_distinct_dst (h : Bool) :
    (links h).Pairwise (fun a b => a.dst≠b.dst) := by
  cases h <;> decide

private theorem prefix_right_frame (hu hv : Bool) (u v : BitVec 96) (k : Fin 3)
    (safe : oldK hv v k=resetForward ∨ oldK hv v k=T) :
    Frames k (rowPrefix (hu,hv) (u,v)).2.2 := by
  let norm := fun j : Fin 3 =>
    let t := oldK hv v j
    if t.fault then putK j t
    else if parked t hv v j && (t.race==1 || t.race==3) then putK j (raceNext t 2)
    else .empty _
  have singles (j : Fin 3) : Frames k (norm j) := by
    by_cases eq : k=j
    · subst j
      rcases safe with S | S
      · simpa [norm,S,resetForward,parked] using empty_frames k
      · simpa [norm,S,T,parked] using empty_frames k
    · dsimp [norm]
      split
      · exact fun x => read_putK_other _ _ eq _ x
      · split
        · exact fun x => read_putK_other _ _ eq _ x
        · exact empty_frames k
  let clear := (resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)
  let base := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else clear
  have base_frame : Frames k base := by
    dsimp [base]
    split
    · split
      · exact keep_high (by decide) _ _
      · exact empty_frames k
    · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
  change Frames k (((base.compose (norm 0)).compose (norm 1)).compose (norm 2))
  exact compose_frames (compose_frames (compose_frames base_frame (singles 0))
    (singles 1)) (singles 2)

/-- An intact trail prevents the incoming selected edge from changing the
next RESET forward or trail slot. Only the freshly installed source K0
can be subject to the independent responder-door action. -/
theorem reset_inbound_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : oldK hv v k=resetForward ∨ oldK hv v k=T) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=(kField k).read v := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k dst)
  have pre_frame (l : Link) (i : l∈pre) : some k≠l.dst := by
    have pw := links_distinct_dst hv
    rw [L] at pw
    have K := (List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp)
    rw [dst] at K
    exact Ne.symm K
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [H,dst,link_trail_guard _ _ _ _ _ _ _ _ _ trail safe,
    fold_right_frame _ _ _ _ _ _ _ _ _ (Z k dst),←H,
    fold_right_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact prefix_right_frame hu hv u v k safe v

#print axioms reset_inbound_frame_pair
private theorem read_covered {n m : Nat} (a : Field 96 n) (b : Field 96 m)
    (v : BitVec m) (x : BitVec 96)
    (lo : b.offset≤a.offset) (hi : a.offset+n≤b.offset+m) :
    a.read ((b.assign v).apply x)=a.read ((b.assign v).apply 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i ilt
  have H := (b.inMask v (a.offset+i)).mpr ⟨by omega,by omega⟩
  simp only [Field.read,BitVec.getLsbD_extractLsb',ilt,decide_true,Bool.true_and]
  rw [Patch.write _ _ _ H,Patch.write _ _ _ H]

/-- The full MIS2 responder door establishes WAIT0 at a genuine RESET0 issue. -/
theorem reset_issue_controller_pair (hu : Bool) (u v : BitVec 96)
    (phase : get v 81 2 (by decide)=1) (op : get v 78 3 (by decide)=0) :
    let q := MISByteRows.row (hu,true) (u,v)
    let z := q.2.apply v
    get z 81 2 (by decide)=2 ∧ get z 78 3 (by decide)=0 := by
  rw [←localRow_eq]
  unfold localRow rowPost
  dsimp only
  rw [reset_issue_source v _ phase op]
  simp only [if_true, Patch.compose_apply]
  let pa : Field 96 2 := lane 81 2 (by decide)
  let pc : Field 96 3 := lane 78 3 (by decide)
  change (pa.read ((putK 0 resetForward).apply ((put 81 2 (by decide) 2).apply
    (resetSource.apply _)))).toNat=2 ∧
    (pc.read ((putK 0 resetForward).apply ((put 81 2 (by decide) 2).apply
    (resetSource.apply _)))).toNat=0
  unfold putK resetSource put
  rw [Field.read_other_assign pa _ _ _ (.inr (by decide)),Field.read_assign,
    Field.read_other_assign pc _ _ _ (.inr (by decide)),
    Field.read_other_assign pc _ _ _ (.inl (by decide)),
    read_covered pc _ _ _ (by decide) (by decide)]
  decide

/-- The full MIS2 responder door establishes ISSUE1 on a RESET0 reply. -/
theorem reset_consume_controller_pair (hu : Bool) (u v : BitVec 96)
    (phase : get v 81 2 (by decide)=2) (op : get v 78 3 (by decide)=0)
    (reply : oldK true v 0=resetReply) :
    let q := MISByteRows.row (hu,true) (u,v)
    let z := q.2.apply v
    get z 81 2 (by decide)=1 ∧ get z 78 3 (by decide)=1 := by
  rw [←localRow_eq]
  unfold localRow rowPost
  dsimp only
  rw [reply,reset_consume_source v phase op]
  simp only [if_true, Patch.compose_apply]
  let pa : Field 96 2 := lane 81 2 (by decide)
  let pc : Field 96 3 := lane 78 3 (by decide)
  change (pa.read ((putK 0 E).apply ((phaseOp 1 1).apply _))).toNat=1 ∧
    (pc.read ((putK 0 E).apply ((phaseOp 1 1).apply _))).toNat=1
  unfold putK phaseOp put
  rw [Field.read_other_assign pa _ _ _ (.inr (by decide)),
    Field.read_other_assign pc _ _ _ (.inr (by decide)),
    read_covered pa _ _ _ (by decide) (by decide),
    read_covered pc _ _ _ (by decide) (by decide)]
  decide

#print axioms reset_issue_controller_pair
#print axioms reset_consume_controller_pair
/-- At a live root the responder door is a no-op on RESET0 forward/trail.
The route fold cannot target responder-header slot zero. -/
theorem reset_root_inbound_frame_pair (hu : Bool) (u v : BitVec 96)
    (wait : get v 81 2 (by decide)=2)
    (op : get v 78 3 (by decide)=0)
    (safe : oldK true v 0=resetForward ∨ oldK true v 0=T) :
    let q := MISByteRows.row (hu,true) (u,v)
    (kField 0).read (q.2.apply v)=(kField 0).read v := by
  have tags : (oldK true v 0).tag=1 ∨ (oldK true v 0).tag=2 := by
    rcases safe with S|S
    · exact .inr (by rw [S]; rfl)
    · exact .inl (by rw [S]; rfl)
  have src := source_wait_holds v (oldK true v 0) wait (by omega) tags
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [post_frame _ _ _ _ (.inr (.inr (congrArg Prod.snd src)))]
  have H (l : Link) (M : l∈links true) : some (0 : Fin 3)≠l.dst := by
    change l∈([⟨0,some 1⟩,⟨1,some 2⟩,⟨2,none⟩] : List Link) at M
    simp only [List.mem_cons,List.not_mem_nil,or_false] at M
    rcases M with A|A|A <;> subst l <;> decide
  rw [fold_right_frame _ _ _ _ _ _ _ _ _ H]
  exact prefix_right_frame hu true u v 0 safe v

#print axioms reset_root_inbound_frame_pair
private theorem prefix_left_trail_frame (hu hv : Bool) (u v : BitVec 96) (k : Fin 3)
    (safe : oldK hu u k=T) :
    Frames k (rowPrefix (hu,hv) (u,v)).2.1 := by
  let norm := fun j : Fin 3 =>
    let t := oldK hu u j
    if t.fault then putK j t
    else if parked t hu u j && (t.race==1 || t.race==2) then putK j (raceNext t 3)
    else .empty _
  have singles (j : Fin 3) : Frames k (norm j) := by
    by_cases eq : k=j
    · subst j
      simpa [norm,safe,T,parked] using empty_frames k
    · dsimp [norm]
      split
      · exact fun x => read_putK_other _ _ eq _ x
      · split
        · exact fun x => read_putK_other _ _ eq _ x
        · exact empty_frames k
  unfold rowPrefix
  dsimp only
  apply compose_frames (compose_frames (compose_frames ?_ (singles 0)) (singles 1)) (singles 2)
  split
  · exact keep_high (by decide) _ _
  · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)

private theorem links_distinct_src (h : Bool) :
    (links h).Pairwise (fun a b => a.src≠b.src) := by
  cases h <;> decide

/-- A trail strictly before its RESET frontier survives the outgoing
edge too: only a reply or empty successor would clear or reverse it. -/
theorem reset_prefix_trail_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : oldK hv v k=resetForward ∨ oldK hv v k=T) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=(kField j).read u := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame (l : Link) (i : l∈pre) : j≠l.src := by
    have pw := links_distinct_src hv
    rw [L] at pw
    exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp))
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  rw [H,dst,link_trail_guard _ _ _ _ _ _ _ _ _ trail safe,
    fold_left_frame _ _ _ _ _ _ _ _ _ A,←H,
    fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact prefix_left_trail_frame hu hv u v j trail u

#print axioms reset_prefix_trail_frame_pair

private theorem reverse_normalizer_right_frame (hu hv : Bool) (u v : BitVec 96) (k : Fin 3)
    (safe : (oldK hv v k).fault=false)
    (park : parked (oldK hv v k) hv v k=false) :
    Frames k (rowPrefix (hu,hv) (u,v)).2.2 := by
  let norm := fun j : Fin 3 =>
    let t := oldK hv v j
    if t.fault then putK j t
    else if parked t hv v j && (t.race==1 || t.race==3) then putK j (raceNext t 2)
    else .empty _
  have singles (j : Fin 3) : Frames k (norm j) := by
    by_cases eq : k=j
    · subst j
      simpa [norm,safe,park] using empty_frames k
    · dsimp [norm]
      split
      · exact fun x => read_putK_other _ _ eq _ x
      · split
        · exact fun x => read_putK_other _ _ eq _ x
        · exact empty_frames k
  let clear := (resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)
  let base := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else clear
  have base_frame : Frames k base := by
    dsimp [base]
    split
    · split
      · exact keep_high (by decide) _ _
      · exact empty_frames k
    · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
  change Frames k (((base.compose (norm 0)).compose (norm 1)).compose (norm 2))
  exact compose_frames (compose_frames (compose_frames base_frame (singles 0))
    (singles 1)) (singles 2)

private theorem reverse_normalizer_left_frame (hu hv : Bool) (u v : BitVec 96) (k : Fin 3)
    (safe : (oldK hu u k).fault=false)
    (park : parked (oldK hu u k) hu u k=false) :
    Frames k (rowPrefix (hu,hv) (u,v)).2.1 := by
  let norm := fun j : Fin 3 =>
    let t := oldK hu u j
    if t.fault then putK j t
    else if parked t hu u j && (t.race==1 || t.race==2) then putK j (raceNext t 3)
    else .empty _
  have singles (j : Fin 3) : Frames k (norm j) := by
    by_cases eq : k=j
    · subst j
      simpa [norm,safe,park] using empty_frames k
    · dsimp [norm]
      split
      · exact fun x => read_putK_other _ _ eq _ x
      · split
        · exact fun x => read_putK_other _ _ eq _ x
        · exact empty_frames k
  unfold rowPrefix
  dsimp only
  apply compose_frames (compose_frames (compose_frames ?_ (singles 0)) (singles 1)) (singles 2)
  split
  · exact keep_high (by decide) _ _
  · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)

private theorem link_cleared_guard (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (ab : Pair (Patch 96)) (j k : Fin 3)
    (safe : oldK hu u j=E ∨ oldK hu u j=resetReply)
    (clear : oldK hv v k=E) :
    linkStep hu hv u v win ab ⟨j,some k⟩=ab := by
  rcases ab with ⟨a,b⟩
  rcases safe with S|S <;> simp [linkStep,S,clear,ready,E,resetReply]

private theorem link_terminal_drained (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (ab : Pair (Patch 96)) (j : Fin 3)
    (safe : oldK hu u j=E ∨ oldK hu u j=resetReply) :
    linkStep hu hv u v win ab ⟨j,none⟩=ab := by
  rcases ab with ⟨a,b⟩
  rcases safe with S|S <;> simp [linkStep,S,ready,E,resetReply]

/-- During return, the departing reply or a cleared lane cannot be
overwritten by its outgoing edge when its successor is cleared. The
terminal case has no successor and is covered separately in the same theorem. -/
theorem reset_reverse_outbound_frame_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (safe : oldK hu u j=E ∨ oldK hu u j=resetReply)
    (clear : ∀ k, destination hv j=some k → oldK hv v k=E) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=(kField j).read u := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame (l : Link) (i : l∈pre) : j≠l.src := by
    have pw := links_distinct_src hv
    rw [L] at pw
    exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp))
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
    (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  have hold : linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩=p := by
    cases a : destination hv j with
    | none => exact link_terminal_drained _ _ _ _ _ _ _ safe
    | some k => exact link_cleared_guard _ _ _ _ _ _ _ _ safe (clear k a)
  rw [hold,fold_left_frame _ _ _ _ _ _ _ _ _ A,
    fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame]
  apply reverse_normalizer_left_frame hu hv u v j
  · rcases safe with S|S <;> rw [S] <;> rfl
  · rcases safe with S|S <;> rw [S] <;> rfl

/-- A cleared suffix lane is untouched by the incoming edge from a
cleared lane or the authentic returning reply. -/
theorem reset_reverse_inbound_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k)
    (safe : oldK hu u j=E ∨ oldK hu u j=resetReply)
    (clear : oldK hv v k=E) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=(kField k).read v := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k dst)
  have pre_frame (l : Link) (i : l∈pre) : some k≠l.dst := by
    have pw := links_distinct_dst hv
    rw [L] at pw
    have K := (List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp)
    rw [dst] at K
    exact Ne.symm K
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [dst,link_cleared_guard _ _ _ _ _ _ _ _ safe clear,
    fold_right_frame _ _ _ _ _ _ _ _ _ (Z k dst),
    fold_right_frame _ _ _ _ _ _ _ _ _ pre_frame]
  apply reverse_normalizer_right_frame hu hv u v k
  · rw [clear]; rfl
  · rw [clear]; rfl

#print axioms reset_reverse_outbound_frame_pair
#print axioms reset_reverse_inbound_frame_pair

set_option maxHeartbeats 2800000

private def ControllerFrame {w : Nat} (f : Field 96 w) (p : Patch 96) : Prop :=
  ∀ x, f.read (p.apply x) = f.read x

private theorem ctl_empty {w : Nat} (f : Field 96 w) : ControllerFrame f (.empty _) := by
  intro x
  congr 1
  change x &&& BitVec.allOnes 96 ||| 0 = x
  rw [BitVec.and_allOnes]
  exact BitVec.or_zero

private theorem ctl_compose {w : Nat} {f : Field 96 w} {p q : Patch 96}
    (P : ControllerFrame f p) (Q : ControllerFrame f q) : ControllerFrame f (p.compose q) := by
  intro x
  rw [Patch.compose_apply,Q,P]

private theorem ctl_put {w : Nat} {f : Field 96 w} (o l : Nat) (fits : o+l≤96) (v : Nat)
    (B : f.offset+w≤o ∨ o+l≤f.offset) : ControllerFrame f (put o l fits v) := by
  intro x
  exact Field.read_other_assign f (lane o l fits) _ _ B

private theorem ctl_k {w : Nat} {f : Field 96 w} (low : 57≤f.offset) (j : Fin 3)
    (t : Token) : ControllerFrame f (putK j t) := by
  intro x
  apply Field.read_other_assign f (kField j) _ _ (.inr ?_)
  change 19*(2-j.val)+19≤f.offset
  omega

private theorem ctl_grants {w : Nat} {f : Field 96 w} (high : f.offset+w≤83)
    (g : Fin 3→Bool) : ControllerFrame f (grantsPatch g) :=
  ctl_put _ _ _ _ (.inl (by omega))

private theorem ctl_seal {w : Nat} {f : Field 96 w} (high : f.offset+w≤83)
    (d : Option Nat) : ControllerFrame f (putSeal d) :=
  ctl_put _ _ _ _ (.inl high)

private theorem ctl_effect {w : Nat} (f : Field 96 w) (high : f.offset+w≤83)
    (u v : BitVec 96) (hu hv : Bool) (l : Link) (win : Bool) (t : Token) :
    ControllerFrame f (effect u v hu hv l.src l.dst win t).1 ∧
      ControllerFrame f (effect u v hu hv l.src l.dst win t).2.1 := by
  unfold effect
  dsimp only
  split
  · exact ⟨ctl_empty f,ctl_empty f⟩
  split
  · split
    · refine ⟨ctl_empty f,?_⟩
      exact ctl_compose (ctl_put (f:=f) 92 1 (by decide) ((t.payload/2)%2)
        (.inl (by omega))) (ctl_seal (f:=f) high none)
    · exact ⟨ctl_empty f,ctl_empty f⟩
  split
  · exact ⟨ctl_empty f,ctl_empty f⟩
  split
  · exact ⟨ctl_seal (f:=f) high none,ctl_empty f⟩
  split
  · exact ⟨ctl_empty f,ctl_empty f⟩
  split
  · split
    · exact ⟨ctl_empty f,ctl_empty f⟩
    · split
      · have H : (t.payload/2)%2<2 := Nat.mod_lt _ (by decide)
        exact ⟨ctl_put (f:=f) (88-(t.payload/2)%2) 1 (by omega)
          (bitAt t.payload 0).toNat (.inl (by omega)), ctl_empty f⟩
      · exact ⟨ctl_seal (f:=f) high (some t.payload),ctl_empty f⟩
  · exact ⟨ctl_empty f,ctl_empty f⟩

private theorem ctl_link {w : Nat} (f : Field 96 w)
    (low : 57≤f.offset) (high : f.offset+w≤83)
    (hu hv : Bool) (u v : BitVec 96) (win : Fin 3→Bool) (p : Pair (Patch 96))
    (l : Link) (X : BitVec 96) :
    f.read ((linkStep hu hv u v win p l).1.apply X)=f.read (p.1.apply X) ∧
    f.read ((linkStep hu hv u v win p l).2.apply X)=f.read (p.2.apply X) := by
  have F := ctl_effect f high u v hu hv l (win l.src) (oldK hu u l.src)
  have K (j : Fin 3) (t : Token) (z : BitVec 96) :
      f.read ((putK j t).apply z)=f.read z := ctl_k low j t z
  have FL (z : BitVec 96) := F.1 z
  have FR (z : BitVec 96) := F.2 z
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · split <;> (constructor <;> first | rfl | simp only [Patch.compose_apply,K,FL,FR])
  · split
    · exact ⟨rfl,rfl⟩
    · split
      · split <;> (constructor <;> first | rfl | simp only [Patch.compose_apply,K])
      · split
        · constructor <;> simp only [Patch.compose_apply,K]
        · split <;> (constructor <;> first | rfl | simp only [Patch.compose_apply,K])

private theorem ctl_fold {w : Nat} (f : Field 96 w)
    (low : 57≤f.offset) (high : f.offset+w≤83)
    (hu hv : Bool) (u v : BitVec 96) (win : Fin 3→Bool) (p : Pair (Patch 96))
    (L : List Link) (X : BitVec 96) :
    f.read ((L.foldl (linkStep hu hv u v win) p).1.apply X)=f.read (p.1.apply X) ∧
    f.read ((L.foldl (linkStep hu hv u v win) p).2.apply X)=f.read (p.2.apply X) := by
  induction L generalizing p with
  | nil => exact ⟨rfl,rfl⟩
  | cons l L ih =>
    have H := ih (linkStep hu hv u v win p l)
    have T := ctl_link f low high hu hv u v win p l X
    exact ⟨H.1.trans T.1,H.2.trans T.2⟩

private theorem ctl_norm {w : Nat} (f : Field 96 w) (low : 57≤f.offset)
    (j : Fin 3) (t q : Token) (b : Bool) :
    ControllerFrame f (if t.fault then putK j t else if b then putK j q else Patch.empty 96) := by
  split
  · exact ctl_k low j t
  · cases b
    · exact ctl_empty f
    · exact ctl_k low j q

private theorem ctl_prefix_left {w : Nat} (f : Field 96 w)
    (low : 57≤f.offset) (high : f.offset+w≤83) (hv : Bool) (u v : BitVec 96) :
    ControllerFrame f (rowPrefix (true,hv) (u,v)).2.1 := by
  unfold rowPrefix
  dsimp only
  simp only [if_true]
  exact ctl_compose (ctl_compose (ctl_compose (ctl_grants high _)
    (ctl_norm f low 0 _ _ _)) (ctl_norm f low 1 _ _ _)) (ctl_norm f low 2 _ _ _)

private theorem ctl_prefix_right {w : Nat} (f : Field 96 w)
    (low : 57≤f.offset) (high : f.offset+w≤83) (hu : Bool) (u v : BitVec 96) :
    ControllerFrame f (rowPrefix (hu,true) (u,v)).2.2 := by
  have P (b : Bool) : ControllerFrame f
      (if b then grantsPatch (canonical v) else Patch.empty 96) := by
    cases b
    · exact ctl_empty f
    · exact ctl_grants high _
  unfold rowPrefix
  dsimp only
  simp only [if_true]
  exact ctl_compose (ctl_compose (ctl_compose (P _)
    (ctl_norm f low 0 _ _ _)) (ctl_norm f low 1 _ _ _)) (ctl_norm f low 2 _ _ _)

/-- The initiator cannot write an eligible short header's source-control
field, even when the old responder or other two lanes carry forged work. -/
theorem source_field_outgoing_pair {w : Nat} (f : Field 96 w)
    (low : 57≤f.offset) (high : f.offset+w≤83) (hv : Bool) (u v : BitVec 96) :
    f.read ((MISByteRows.row (true,hv) (u,v)).1.apply u)=f.read u := by
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [rowPost_left]
  exact (ctl_fold f low high true hv u v _ _ _ u).1.trans
    (ctl_prefix_left f low high hv u v u)

/-- A held responder door sources no controller change on an incoming
mark; the concurrent route and all other old lanes also leave it intact. -/
theorem source_field_held_inbound_pair {w : Nat} (f : Field 96 w)
    (low : 57≤f.offset) (high : f.offset+w≤83) (hu : Bool) (u v : BitVec 96)
    (H : source v (oldK true v 0) = (.empty _,none)) :
    f.read ((MISByteRows.row (hu,true) (u,v)).2.apply v)=f.read v := by
  rw [←localRow_eq]
  unfold localRow rowPost
  dsimp only
  rw [H]
  simp only [if_true,Patch.compose_apply]
  have Z (z : BitVec 96) : f.read ((Patch.empty 96).apply z)=f.read z := ctl_empty f z
  rw [Z,Z]
  exact (ctl_fold f low high hu true u v _ _ _ v).2.trans
    (ctl_prefix_right f low high hu u v v)

#print axioms source_field_outgoing_pair
#print axioms source_field_held_inbound_pair


/-- One nominated outgoing incident mark promotes a parked ADMIT from
race 1 to 3 or from race 2 to 4 in the actual MIS work pair. The latter
is ready; the mark observes the old byte so it does not advance yet. -/
theorem parked_admit_left_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (t : Token) (old : oldK hu u j=t) (tag : t.tag=2) (opcode : t.opcode=2)
    (live : t.fault=false) (gate : atGate hu u j=true)
    (race : t.race=1 ∨ t.race=2) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode { t with race := if t.race=1 then 3 else 4 } := by
  have P : parked t hu u j=true := by simp [parked,tag,opcode,live,gate]
  have lt : t.race<4 := by rcases race with H|H <;> omega
  have norm : (t.race==1 || t.race==2)=true := by
    rcases race with H|H <;> simp [H]
  have step : raceNext t 3={t with race := if t.race=1 then 3 else 4} := by
    rcases race with H|H <;> simp [raceNext,H]
  have idle (win : Fin 3 → Bool) (p : Pair (Patch 96)) (d : Option (Fin 3)) :
      linkStep hu hv u v win p ⟨j,d⟩=p := by
    rcases p with ⟨a,b⟩
    simp [linkStep,old,ready,P,lt,tag]
  have pre_norm : (kField j).read ((rowPrefix (hu,hv) (u,v)).2.1.apply u)=
      encode { t with race := if t.race=1 then 3 else 4 } := by
    let normal := fun k : Fin 3 =>
      let z := oldK hu u k
      if z.fault then putK k z
      else if parked z hu u k && (z.race==1 || z.race==2) then putK k (raceNext z 3)
      else .empty _
    have selected : normal j=putK j (raceNext t 3) := by
      dsimp only [normal]
      rw [old,live,P,norm]
      rfl
    have other (k : Fin 3) (N : j≠k) : Frames j (normal k) := by
      dsimp only [normal]
      split
      · exact fun z=>read_putK_other _ _ N _ z
      · split
        · exact fun z=>read_putK_other _ _ N _ z
        · exact empty_frames j
    let base := (if hu then
      grantsPatch (fun k => (canonical u k && !(hu && ready hu u k (oldK hu u k) &&
          !(oldK hu u k).fault && (oldK hu u k).opcode==0)) ||
        (rowPrefix (hu,hv) (u,v)).1 k)
      else ((resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)))
    change (kField j).read ((((base.compose (normal 0)).compose (normal 1)).compose (normal 2)).apply u)=_
    have js : j=0 ∨ j=1 ∨ j=2 := by
      have J := j.isLt
      have H : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
      rcases H with H|H|H
      · exact .inl (Fin.ext H)
      · exact .inr (.inl (Fin.ext H))
      · exact .inr (.inr (Fin.ext H))
    rcases js with rfl|rfl|rfl
    · rw [Patch.compose_apply,(other 2 (by decide)),Patch.compose_apply,(other 1 (by decide)),
        Patch.compose_apply,selected,read_putK,step]
    · rw [Patch.compose_apply,(other 2 (by decide)),Patch.compose_apply,selected,read_putK,step]
    · rw [Patch.compose_apply,selected,read_putK,step]
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame (l : Link) (i : l∈pre) : j≠l.src := by
    have pw := links_distinct_src hv
    rw [L] at pw
    exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp))
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  rw [idle,fold_left_frame _ _ _ _ _ _ _ _ _ A,
    fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact pre_norm

#print axioms parked_admit_left_pair

/-- A parked ADMIT with no old F on its unique supplying predecessor
sees the actual incoming mark: race 1→2 or race 3→5. A header's own
source lane cannot be a chart successor and is not silently credited. -/
theorem parked_admit_right_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (upstream : (oldK hu u j).tag≠2)
    (t : Token) (old : oldK hv v k=t) (tag : t.tag=2) (opcode : t.opcode=2)
    (live : t.fault=false) (gate : atGate hv v k=true)
    (race : t.race=1 ∨ t.race=3) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=encode { t with race := if t.race=1 then 2 else 5 } := by
  have P : parked t hv v k=true := by simp [parked,tag,opcode,live,gate]
  have norm : (t.race==1 || t.race==3)=true := by
    rcases race with H|H <;> simp [H]
  have step : raceNext t 2={t with race := if t.race=1 then 2 else 5} := by
    rcases race with H|H <;> simp [raceNext,H]
  have idle (win : Fin 3 → Bool) (p : Pair (Patch 96)) :
      linkStep hu hv u v win p ⟨j,some k⟩=p := by
    rcases p with ⟨a,b⟩
    simp [linkStep,old,ready,upstream,tag]
  have pre_norm : (kField k).read ((rowPrefix (hu,hv) (u,v)).2.2.apply v)=
      encode { t with race := if t.race=1 then 2 else 5 } := by
    let normal := fun a : Fin 3 =>
      let z := oldK hv v a
      if z.fault then putK a z
      else if parked z hv v a && (z.race==1 || z.race==3) then putK a (raceNext z 2)
      else .empty _
    have selected : normal k=putK k (raceNext t 2) := by
      dsimp only [normal]
      rw [old,live,P,norm]
      rfl
    have other (a : Fin 3) (N : k≠a) : Frames k (normal a) := by
      dsimp only [normal]
      split
      · exact fun z=>read_putK_other _ _ N _ z
      · split
        · exact fun z=>read_putK_other _ _ N _ z
        · exact empty_frames k
    let base := if hv then
      if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
      else ((resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false))
    change (kField k).read ((((base.compose (normal 0)).compose (normal 1)).compose (normal 2)).apply v)=_
    have js : k=0 ∨ k=1 ∨ k=2 := by
      have J := k.isLt
      have H : k.val=0 ∨ k.val=1 ∨ k.val=2 := by omega
      rcases H with H|H|H
      · exact .inl (Fin.ext H)
      · exact .inr (.inl (Fin.ext H))
      · exact .inr (.inr (Fin.ext H))
    rcases js with rfl|rfl|rfl
    · rw [Patch.compose_apply,(other 2 (by decide)),Patch.compose_apply,(other 1 (by decide)),
        Patch.compose_apply,selected,read_putK,step]
    · rw [Patch.compose_apply,(other 2 (by decide)),Patch.compose_apply,selected,read_putK,step]
    · rw [Patch.compose_apply,selected,read_putK,step]
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k link)
  have pre_frame (a : Link) (i : a∈pre) : some k≠a.dst := by
    have pw := links_distinct_dst hv
    rw [L] at pw
    have K := (List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp)
    rw [link] at K
    exact Ne.symm K
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [link,idle,fold_right_frame _ _ _ _ _ _ _ _ _ (Z k link),
    fold_right_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact pre_norm

#print axioms parked_admit_right_pair


/-- A subsequent outgoing mark actually moves a ready ADMIT. Its
reservation is converted to the selected payload, then the old target
geometry alone decides whether the forwarded byte enters another gate. -/
theorem ready_admit_out_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (t : Token)
    (old : oldK hu u j=t) (tag : t.tag=2) (opcode : t.opcode=2)
    (live : t.fault=false) (gate : atGate hu u j=true)
    (race : t.race=4 ∨ t.race=5) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode T ∧
    (kField k).read (q.2.apply v)=
      encode { t with race := if atGate hv v k then 1 else 0, payload := t.race-4 } := by
  have P : parked t hu u j=true := by simp [parked,tag,opcode,live,gate]
  have lt : ¬ t.race<4 := by rcases race with H|H <;> omega
  have run (win : Fin 3 → Bool) (a b : Patch 96) :
      linkStep hu hv u v win (a,b) ⟨j,some k⟩ =
        (a.compose (putK j T),b.compose (putK k
          { t with race := if atGate hv v k then 1 else 0, payload := t.race-4 })) := by
    unfold linkStep
    simp only [old, ready, P, tag, beq_self_eq_true, lt, decide_false, Bool.and_false,
      Bool.not_false, Bool.and_true, if_true]
    by_cases G : atGate hv v k=true <;> simp [effect,tag,opcode,live,P,arrival,compose_empty,G]
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k link)
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change
    (kField j).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).1.apply u)=_ ∧
    (kField k).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).2.apply v)=_
  rw [H,link,run]
  constructor
  · rw [rowPost_left,fold_left_frame _ _ _ _ _ _ _ _ _ A,Patch.compose_apply,read_putK]
  · rw [post_frame _ _ _ _ (post.imp_right .inl),fold_right_frame _ _ _ _ _ _ _ _ _ (Z k link),
      Patch.compose_apply,read_putK]

#print axioms ready_admit_out_pair


/-- One selected decoded forward lane is scheduled on this mark. -/
def forwardReady (hu : Bool) (u : BitVec 96) (j : Fin 3) : Bool :=
  ready hu u j (oldK hu u j)

/-- Exact outgoing packet for any inherited ready byte, not just for
authentic RESET0 or ADMIT. The old writer win is from the entire row. -/
def forwardPacket (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3) : Token :=
  let win := (rowPrefix (hu,hv) (u,v)).1 j
  arrival hv v k (effect u v hu hv j (some k) win (oldK hu u j)).2.2

def turnPacket (hu hv : Bool) (u v : BitVec 96) (j : Fin 3) : Token :=
  let win := (rowPrefix (hu,hv) (u,v)).1 j
  terminal (effect u v hu hv j none win (oldK hu u j)).2.2

/-- Selected ready-forward lanes overwrite their exact successor,
and all other work in the simultaneous old-pair row leaves these
writes intact. -/
theorem forward_ready_out_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (front : forwardReady hu u j=true) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode T ∧
    (kField k).read (q.2.apply v)=encode (forwardPacket hu hv u v j k) := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k dst)
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  let ef := effect u v hu hv j (some k) (pr.1 j) (oldK hu u j)
  have step : linkStep hu hv u v pr.1 p ⟨j,some k⟩ =
      ((p.1.compose ef.1).compose (putK j T),
       (p.2.compose ef.2.1).compose (putK k (forwardPacket hu hv u v j k))) := by
    obtain ⟨a,b,E⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
    rw [E]
    unfold linkStep
    dsimp only
    have pre : ready hu u j (oldK hu u j)=true := front
    rw [if_pos pre]
    rfl
  change
    (kField j).read ((rowPost hv v (suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).1.apply u)=_ ∧
    (kField k).read ((rowPost hv v (suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).2.apply v)=_
  rw [dst,step]
  constructor
  · rw [rowPost_left,fold_left_frame _ _ _ _ _ _ _ _ _ A,Patch.compose_apply,read_putK]
  · rw [post_frame _ _ _ _ (post.imp_right .inl),fold_right_frame _ _ _ _ _ _ _ _ _ (Z k dst),
      Patch.compose_apply,read_putK]

/-- Terminal inherited ready forward produces exactly the codec reply
or fault. The other selected links cannot clobber it. -/
theorem forward_ready_turn_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (dst : destination hv j=none) (front : forwardReady hu u j=true) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode (turnPacket hu hv u v j) := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  let ef := effect u v hu hv j none (pr.1 j) (oldK hu u j)
  have step : linkStep hu hv u v pr.1 p ⟨j,none⟩ =
      ((p.1.compose ef.1).compose (putK j (turnPacket hu hv u v j)),p.2.compose ef.2.1) := by
    obtain ⟨a,b,E⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
    rw [E]
    unfold linkStep
    dsimp only
    have pre : ready hu u j (oldK hu u j)=true := front
    rw [if_pos pre]
    rfl
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  rw [dst,step,fold_left_frame _ _ _ _ _ _ _ _ _ A,Patch.compose_apply,read_putK]

#print axioms forward_ready_out_pair
#print axioms forward_ready_turn_pair

set_option maxRecDepth 8192

private def FwdShape (t : Token) : Prop :=
  t.tag=2 ∧ t.opcode<8 ∧ t.race<8 ∧ t.outcome=0 ∧ t.payload<256

private theorem FwdShape.low {t : Token} (H : FwdShape t) :
    L4.ShortPacketTag.lowCode t<2^17 :=
  L4.ShortPacketTag.forward_low_bound t H.2.1 H.2.2.1 H.2.2.2.1 H.2.2.2.2

private theorem payload_upper (p k : Nat) (b : Bool) : setPLane p k b≤p+2^k := by
  unfold setPLane
  split
  · split
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)
  · split
    · exact Nat.le_refl _
    · exact Nat.le_add_right _ _

private theorem fwd_effect_shape (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (k : Option (Fin 3)) (win : Bool) (t : Token) (H : FwdShape t)
    (tiny : t.payload<128) :
    FwdShape (effect u v hu hv j k win t).2.2 := by
  rcases H with ⟨G,O,R,A,P⟩
  have H : FwdShape t := ⟨G,O,R,A,P⟩
  have bad : FwdShape (faultToken 2) := by unfold FwdShape; decide
  unfold effect
  dsimp only
  split
  · exact H
  split
  · split
    · exact ⟨G,O,R,A,P⟩
    · exact bad
  split
  · exact ⟨G,O,by change (0:Nat)<8; decide,A,by change t.race-4<256; omega⟩
  split
  · exact H
  split
  · apply (show ∀ p, p<256 → FwdShape {t with payload := p} from
      fun _ B=>⟨G,O,R,A,B⟩)
    by_cases W : win=true
    · rw [if_pos W]
      let p := setPLane t.payload (5-j.val) (selector u==1)
      have a := payload_upper t.payload (5-j.val) (selector u==1)
      have b := payload_upper p (2-j.val) (bank u (selector u))
      have ua : 2^(5-j.val)≤32 := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      have ub : 2^(2-j.val)≤4 := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      change p≤t.payload+2^(5-j.val) at a
      change setPLane p (2-j.val) (bank u (selector u))<256
      omega
    · rw [if_neg W]
      have Z : setPLane t.payload 6 false≤t.payload := by
        unfold setPLane
        split <;> simp only [Bool.false_eq_true,if_false] <;> omega
      omega
  split
  · split
    · exact bad
    · split <;> exact H
  · exact H

private theorem fwd_arrival_shape (hv : Bool) (v : BitVec 96) (k : Fin 3) (t : Token)
    (H : FwdShape t) : FwdShape (arrival hv v k t) := by
  unfold arrival
  split
  · exact ⟨H.1,H.2.1,by change (1:Nat)<8; decide,H.2.2.2⟩
  · exact H

private theorem fwd_bound_of_ready (h : Bool) (x : BitVec 96) (j : Fin 3)
    (R : forwardReady h x j=true) :
    FwdShape (oldK h x j) ∧ (oldK h x j).payload<128 := by
  have RR := R
  unfold forwardReady ready at RR
  have tag : (oldK h x j).tag=2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp RR).1
  have V := L4.ShortPacketTag.decoded_forward_bounds (atGate h x j) ((kField j).read x) tag
  change (oldK h x j).opcode<8 ∧ (oldK h x j).race<8 ∧
    (oldK h x j).outcome=0 ∧ (oldK h x j).payload<128 at V
  exact ⟨⟨tag,V.1,V.2.1,V.2.2.1,Nat.lt_trans V.2.2.2 (by decide)⟩,V.2.2.2⟩

/-- Ready inherited forwards remain forwards after arbitrary effect,
including a fault introduced by a refused or stale request. -/
theorem forwardPacket_tag (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (fr : forwardReady hu u j=true) (g : Bool) :
    (decode g (encode (forwardPacket hu hv u v j k))).tag=2 := by
  obtain ⟨B,S⟩ := fwd_bound_of_ready hu u j fr
  have P : FwdShape (forwardPacket hu hv u v j k) :=
    fwd_arrival_shape hv v k _ (fwd_effect_shape hu hv u v j _ _ _ B S)
  rw [L4.ShortPacketTag.inherited_encode_tag _ g P.low (by rw [P.1]; decide),P.1]

private theorem terminal_tag_low (t : Token) (H : FwdShape t) :
    (terminal t).tag=3 ∧ L4.ShortPacketTag.lowCode (terminal t)<2^17 := by
  rcases H with ⟨G,O,R,A,P⟩
  unfold terminal
  split
  · decide
  split
  · split
    · refine ⟨rfl,?_⟩
      simp [L4.ShortPacketTag.lowCode]
      have M := Nat.mod_lt t.payload (by decide : 0<64)
      omega
    · decide
  · refine ⟨rfl,?_⟩
    have T : (if t.opcode==2 then t.payload else 0)<256 := by split <;> omega
    simp only [L4.ShortPacketTag.lowCode, Bool.toNat_false, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    omega

/-- Any inherited ready terminal produces a reply tag, including all
faults, without assuming that the payload is authentic. -/
theorem turnPacket_tag (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (fr : forwardReady hu u j=true) (g : Bool) :
    (decode g (encode (turnPacket hu hv u v j))).tag=3 := by
  obtain ⟨B,S⟩ := fwd_bound_of_ready hu u j fr
  have P : (turnPacket hu hv u v j).tag=3 ∧
      L4.ShortPacketTag.lowCode (turnPacket hu hv u v j)<2^17 :=
    terminal_tag_low _ (fwd_effect_shape hu hv u v j _ _ _ B S)
  rw [L4.ShortPacketTag.inherited_encode_tag _ g P.2 (by rw [P.1]; decide),P.1]

#print axioms forwardPacket_tag
#print axioms turnPacket_tag

/-- An arbitrary inherited non-forward byte is held literally unless
the row canonicalizes a declared reply fault. -/
def normalizedNoForward (h : Bool) (x : BitVec 96) (j : Fin 3) : BitVec 19 :=
  let t := oldK h x j
  if t.fault then encode t else (kField j).read x

private theorem dirty_three_normalizers (j : Fin 3) (x : BitVec 96)
    (base : Patch 96) (p : Fin 3→Patch 96) (t : Token)
    (safe : p j=(if t.fault then putK j t else .empty _))
    (fr : Frames j base)
    (outer : ∀ k, j≠k → Frames j (p k)) :
    (kField j).read ((((base.compose (p 0)).compose (p 1)).compose (p 2)).apply x) =
      if t.fault then encode t else (kField j).read x := by
  have J := j.isLt
  have js : j=0 ∨ j=1 ∨ j=2 := by
    have H : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
    rcases H with H|H|H
    · exact .inl (Fin.ext H)
    · exact .inr (.inl (Fin.ext H))
    · exact .inr (.inr (Fin.ext H))
  have selected (u : BitVec 96) (K : (kField j).read u=(kField j).read x) :
      (kField j).read ((p j).apply u)=if t.fault then encode t else (kField j).read x := by
    rw [safe]
    split
    · exact read_putK _ _ _
    · rw [empty_frames j u,K]
  rcases js with rfl|rfl|rfl
  · rw [Patch.compose_apply,outer 2 (by decide),Patch.compose_apply,outer 1 (by decide),
      Patch.compose_apply]
    exact selected _ (fr x)
  · rw [Patch.compose_apply,outer 2 (by decide),Patch.compose_apply]
    apply selected
    rw [Patch.compose_apply,outer 0 (by decide)]
    exact fr x
  · rw [Patch.compose_apply]
    apply selected
    rw [Patch.compose_apply,outer 1 (by decide),Patch.compose_apply,outer 0 (by decide)]
    exact fr x

private theorem dirty_left_norm (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (no : (oldK hu u j).tag≠2) :
    (kField j).read ((rowPrefix (hu,hv) (u,v)).2.1.apply u)=normalizedNoForward hu u j := by
  let p := fun k : Fin 3 =>
    let t := oldK hu u k
    if t.fault then putK k t
    else if parked t hu u k && (t.race==1 || t.race==2) then putK k (raceNext t 3)
    else .empty _
  let base := (if hu then
      grantsPatch (fun k => (canonical u k && !(hu && ready hu u k (oldK hu u k) &&
          !(oldK hu u k).fault && (oldK hu u k).opcode==0)) ||
        (rowPrefix (hu,hv) (u,v)).1 k)
      else ((resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)))
  change (kField j).read ((((base.compose (p 0)).compose (p 1)).compose (p 2)).apply u)=_
  apply dirty_three_normalizers
  · simp [p,parked,no]
  · dsimp [base]
    split
    · exact keep_high (by decide) _ _
    · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
  · intro k N
    dsimp only [p]
    split
    · exact fun z=>read_putK_other _ _ N _ z
    · split
      · exact fun z=>read_putK_other _ _ N _ z
      · exact empty_frames j

private theorem dirty_right_norm (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (no : (oldK hv v j).tag≠2) :
    (kField j).read ((rowPrefix (hu,hv) (u,v)).2.2.apply v)=normalizedNoForward hv v j := by
  let p := fun k : Fin 3 =>
    let t := oldK hv v k
    if t.fault then putK k t
    else if parked t hv v k && (t.race==1 || t.race==3) then putK k (raceNext t 2)
    else .empty _
  let base := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else ((resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false))
  change (kField j).read ((((base.compose (p 0)).compose (p 1)).compose (p 2)).apply v)=_
  apply dirty_three_normalizers
  · simp [p,parked,no]
  · dsimp [base]
    split
    · split
      · exact keep_high (by decide) _ _
      · exact empty_frames j
    · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
  · intro k N
    dsimp only [p]
    split
    · exact fun z=>read_putK_other _ _ N _ z
    · split
      · exact fun z=>read_putK_other _ _ N _ z
      · exact empty_frames j

private theorem dirty_pre_left (h : Bool) (j : Fin 3) (pre suf : List Link)
    (L : links h=pre++⟨j,destination h j⟩::suf) :
    ∀ l∈pre,j≠l.src := by
  intro l M
  have pw := links_distinct_src h
  rw [L] at pw
  exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ M ⟨j,destination h j⟩ (by simp))

private theorem dirty_pre_right (h : Bool) (j k : Fin 3) (pre suf : List Link)
    (L : links h=pre++⟨j,destination h j⟩::suf) (dst : destination h j=some k) :
    ∀ l∈pre,some k≠l.dst := by
  intro l M
  have pw := links_distinct_dst h
  rw [L] at pw
  have K := (List.pairwise_append.mp pw).2.2 _ M ⟨j,destination h j⟩ (by simp)
  rw [dst] at K
  exact Ne.symm K

/-- The actual terminal row removes old T and otherwise holds the
inherited no-forward class, with the row's literal normalization. -/
theorem dirty_nonforward_terminal_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (terminal : destination hv j=none) (no : (oldK hu u j).tag≠2) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=
      if (oldK hu u j).tag=1 then encode E else normalizedNoForward hu u j := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame := dirty_pre_left hv j pre suf L
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
    (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  obtain ⟨a,b,H⟩ : ∃ a b,p=(a,b) := ⟨p.1,p.2,rfl⟩
  rw [H,terminal]
  by_cases trail : (oldK hu u j).tag=1
  · have eq : linkStep hu hv u v pr.1 (a,b) ⟨j,none⟩=(a.compose (putK j E),b) := by
      simp [linkStep,ready,trail]
    rw [eq,fold_left_frame _ _ _ _ _ _ _ _ _ A,Patch.compose_apply,read_putK,if_pos trail]
  · have eq : linkStep hu hv u v pr.1 (a,b) ⟨j,none⟩=(a,b) := by
      simp [linkStep,ready,no,trail]
    rw [eq,fold_left_frame _ _ _ _ _ _ _ _ _ A,←H,
      fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame,if_neg trail]
    exact dirty_left_norm hu hv u v j no

/-- A right reply transits toward the source even through dirty old
E/T/D at the predecessor. The preserving write is the normalized
decoded old reply, and the right lane becomes canonical E. -/
theorem dirty_nonforward_reply_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (no : (oldK hu u j).tag≠2)
    (reply : (oldK hv v k).tag=3) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode (oldK hv v k) ∧
    (kField k).read (q.2.apply v)=encode E := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k link)
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b,p=(a,b) := ⟨p.1,p.2,rfl⟩
  change
    (kField j).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).1.apply u)=_ ∧
    (kField k).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).2.apply v)=_
  have eq : linkStep hu hv u v pr.1 (a,b) ⟨j,some k⟩=
      (a.compose (putK j (oldK hv v k)),b.compose (putK k E)) := by
    simp [linkStep,ready,no,reply]
  rw [H,link,eq]
  constructor
  · rw [rowPost_left,fold_left_frame _ _ _ _ _ _ _ _ _ A,Patch.compose_apply,read_putK]
  · rw [post_frame _ _ _ _ (post.imp_right .inl),fold_right_frame _ _ _ _ _ _ _ _ _ (Z k link),
    Patch.compose_apply,read_putK]

/-- The supplying non-forward lane does not fill old E. It removes
an old T; an old E/D is held, modulo its literal fault normalization. -/
theorem dirty_nonforward_empty_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (no : (oldK hu u j).tag≠2)
    (empty : (oldK hv v k).tag=0) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=
      (if (oldK hu u j).tag=1 then encode E else normalizedNoForward hu u j) ∧
    (kField k).read (q.2.apply v)=normalizedNoForward hv v k := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,Z⟩ := link_split hv j
  have preL := dirty_pre_left hv j pre suf L
  have preR := dirty_pre_right hv j k pre suf L link
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k link)
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b,p=(a,b) := ⟨p.1,p.2,rfl⟩
  change
    (kField j).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).1.apply u)=_ ∧
    (kField k).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).2.apply v)=_
  have eq : linkStep hu hv u v pr.1 (a,b) ⟨j,some k⟩=
      ((if (oldK hu u j).tag=1 then a.compose (putK j E) else a),b) := by
    simp [linkStep,ready,no,empty]
    split <;> rfl
  rw [H,link,eq]
  constructor
  · rw [rowPost_left,fold_left_frame _ _ _ _ _ _ _ _ _ A]
    split
    · rw [Patch.compose_apply,read_putK]
    · have ha := congrArg Prod.fst H
      change p.1=a at ha
      rw [←ha,fold_left_frame _ _ _ _ _ _ _ _ _ preL]
      exact dirty_left_norm hu hv u v j no
  · rw [post_frame _ _ _ _ (post.imp_right .inl),fold_right_frame _ _ _ _ _ _ _ _ _ (Z k link)]
    have hb := congrArg Prod.snd H
    change p.2=b at hb
    rw [←hb,fold_right_frame _ _ _ _ _ _ _ _ _ preR]
    exact dirty_right_norm hu hv u v k (by omega)

#print axioms dirty_nonforward_terminal_pair
#print axioms dirty_nonforward_reply_pair
#print axioms dirty_nonforward_empty_pair

/-- A dirty inherited trail on the right cannot alter a non-forward
supplier, and is itself held. -/
theorem dirty_nonforward_trail_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (no : (oldK hu u j).tag≠2)
    (trail : (oldK hv v k).tag=1) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=
      normalizedNoForward hu u j ∧
    (kField k).read (q.2.apply v)=normalizedNoForward hv v k := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,Z⟩ := link_split hv j
  have preL := dirty_pre_left hv j pre suf L
  have preR := dirty_pre_right hv j k pre suf L link
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k link)
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b,p=(a,b) := ⟨p.1,p.2,rfl⟩
  change
    (kField j).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).1.apply u)=_ ∧
    (kField k).read ((rowPost hv v
      (suf.foldl (linkStep hu hv u v pr.1) (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩))).2.apply v)=_
  have eq : linkStep hu hv u v pr.1 (a,b) ⟨j,some k⟩=(a,b) := by
    simp [linkStep,ready,no,trail]
  rw [H,link,eq]
  constructor
  · rw [rowPost_left,fold_left_frame _ _ _ _ _ _ _ _ _ A]
    have ha := congrArg Prod.fst H
    change p.1=a at ha
    rw [←ha,fold_left_frame _ _ _ _ _ _ _ _ _ preL]
    exact dirty_left_norm hu hv u v j no
  · rw [post_frame _ _ _ _ (post.imp_right .inl),fold_right_frame _ _ _ _ _ _ _ _ _ (Z k link)]
    have hb := congrArg Prod.snd H
    change p.2=b at hb
    rw [←hb,fold_right_frame _ _ _ _ _ _ _ _ _ preR]
    exact dirty_right_norm hu hv u v k (by omega)


#print axioms dirty_nonforward_trail_pair

set_option maxHeartbeats 4000000

private def gfield : Field 96 3 := lane 89 3 (by decide)
private def sfield : Field 96 4 := lane 83 4 (by decide)

private theorem grant_effect_left (u v : BitVec 96) (hv : Bool) (l : Link) (w : Bool) (t : Token) :
    ControllerFrame gfield (effect u v true hv l.src l.dst w t).1 := by
  unfold effect
  dsimp only
  split
  · apply ctl_empty
  split
  · split <;> apply ctl_empty
  split
  · apply ctl_empty
  split
  · exact ctl_put _ _ _ _ (.inr (by decide))
  split
  · apply ctl_empty
  split
  · split
    · apply ctl_empty
    · split
      · exact ctl_put _ _ _ _ (.inr (by change 88-(t.payload/2)%2+1≤89; omega))
      · exact ctl_put _ _ _ _ (.inr (by decide))
  · apply ctl_empty

private theorem link_left_read_of_effect {n : Nat} (f : Field 96 n) (low : 57≤f.offset)
    (hv : Bool) (u v : BitVec 96) (w : Fin 3→Bool) (p : Pair (Patch 96)) (l : Link)
    (F : ControllerFrame f (effect u v true hv l.src l.dst (w l.src) (oldK true u l.src)).1) :
    f.read ((linkStep true hv u v w p l).1.apply u)=f.read (p.1.apply u) := by
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      f.read ((putK j t).apply x)=f.read x := ctl_k low j t x
  have H (x : BitVec 96) := F x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · split <;> simp only [Patch.compose_apply,K,H]
  · split
    · rfl
    · split
      · split <;> first | rfl | simp only [Patch.compose_apply,K]
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> first | rfl | simp only [Patch.compose_apply,K]

private theorem grant_fold_left (hv : Bool) (u v : BitVec 96) (w : Fin 3→Bool)
    (p : Pair (Patch 96)) (L : List Link) :
    gfield.read ((L.foldl (linkStep true hv u v w) p).1.apply u)=gfield.read (p.1.apply u) := by
  induction L generalizing p with
  | nil => rfl
  | cons l tail ih =>
    exact (ih _).trans (link_left_read_of_effect gfield (by decide) hv u v w p l
      (grant_effect_left u v hv l _ _))

private theorem grant_prefix_left (hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (h : oldK true u j=resetForward) :
    (gfield.read ((rowPrefix (true,hv) (u,v)).2.1.apply u)).getLsbD (2-j.val)=false := by
  let rel := fun k : Fin 3 =>
    let t := oldK true u k
    ready true u k t && !t.fault && t.opcode==0
  let ask := fun k : Fin 3 =>
    let t := oldK true u k
    ready true u k t && !t.fault && t.opcode==3
  let w := !canonical u 0 && !canonical u 1 && !canonical u 2 && ask 1 && !rel 1
  let win := fun k : Fin 3 => if k==1 then w
      else !w && !canonical u 1 && ask k && !canonical u k && !rel k
  let gg := fun k => (canonical u k && !rel k) || win k
  have norm (k : Fin 3) (t q : Token) (b : Bool) (x : BitVec 96) :=
    ctl_norm gfield (by decide) k t q b x
  unfold rowPrefix
  dsimp only
  simp only [if_true,Bool.true_and,Patch.compose_apply,norm]
  change (gfield.read ((grantsPatch gg).apply u)).getLsbD (2-j.val)=false
  change ((lane 89 3 (by decide)).read ((lane 89 3 (by decide)).assign
    (BitVec.ofNat 3 (4*(gg 0).toNat+2*(gg 1).toNat+(gg 2).toNat)) |>.apply u)).getLsbD _ = false
  rw [Field.read_assign]
  have rr : rel j=true := by simp [rel,h,resetForward,ready,parked]
  have aa : ask j=false := by simp [ask,h,resetForward]
  have gg_j : gg j=false := by
    unfold gg win
    by_cases k : j=1
    · subst j
      simp [rr,w]
    · simp [rr,k,aa]
  have allj : j=0 ∨ j=1 ∨ j=2 := by
    have h := j.isLt
    rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with a|a|a
    · exact Or.inl (Fin.ext a)
    · exact Or.inr (Or.inl (Fin.ext a))
    · exact Or.inr (Or.inr (Fin.ext a))
  rcases allj with rfl|rfl|rfl
  · cases A : gg 1 <;> cases B : gg 2 <;> rw [gg_j] <;> decide
  · cases A : gg 0 <;> cases B : gg 2 <;> rw [gg_j] <;> decide
  · cases A : gg 0 <;> cases B : gg 1 <;> rw [gg_j] <;> decide

/-- Actual RESET0 departure from an eligible header clears its own grant,
including when the old grant vector was conflicting. -/
theorem reset_release_grant_pair (hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (h : oldK true u j=resetForward) :
    (((BStarShort.shortMIS (true,hv) (u,v)).1.apply u).getLsbD (91-j.val))=false := by
  have kl : 2-j.val<3 := by omega
  have O : ((gfield.read ((MISByteRows.row (true,hv) (u,v)).1.apply u)).getLsbD
      (2-j.val))=false := by
    rw [←localRow_eq]
    unfold localRow
    dsimp only
    rw [rowPost_left,grant_fold_left]
    exact grant_prefix_left hv u v j h
  have IX : 89+(2-j.val)=91-j.val := by have := j.isLt; omega
  unfold gfield Field.read at O
  simp only [lane,BitVec.getLsbD_extractLsb',kl,decide_true,Bool.true_and,IX] at O
  have ND : (BStarShort.grantView 89 3 true u (oldK true u)).drop j=false := by
    simp [BStarShort.GrantView.drop,BStarShort.grantView,h,resetForward]
  have EH : (BStarShort.grantErase (w:=96) 89 (BStarShort.grantView 89 3 true u
      (oldK true u))).getLsbD (91-j.val)=false := by
    rw [BStarShort.grantErase_mask]
    match j with
    | ⟨0,_⟩ => simpa using ND
    | ⟨1,_⟩ => simpa using ND
    | ⟨2,_⟩ => simpa using ND
  have q := BStarShort.shortMIS_mask (true,hv) (u,v) (91-j.val)
  dsimp only [Prod.fst, Prod.snd] at q
  rw [EH] at q
  have B : 91-j.val<96 := by omega
  unfold Patch.apply at O ⊢
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,B,decide_true,
    Bool.true_and] at O ⊢
  rw [q]
  simpa [BStarShort.shortMIS,BStarShort.erase] using O

#print axioms reset_release_grant_pair

private theorem seal_effect_frame_noncenter (u v : BitVec 96) (hv : Bool) (l : Link)
    (w : Bool) (t : Token) (nz : l.src≠1) :
    ControllerFrame sfield (effect u v true hv l.src l.dst w t).1 := by
  unfold effect
  dsimp only
  have z : (l.src==1)=false := Bool.eq_false_iff.mpr (fun H => nz (beq_iff_eq.mp H))
  simp only [z,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]
  split
  · apply ctl_empty
  split
  · split <;> apply ctl_empty
  split
  · apply ctl_empty
  split <;> apply ctl_empty

private theorem seal_center_link (hv : Bool) (u v : BitVec 96) (w : Fin 3→Bool)
    (p : Pair (Patch 96)) (k : Option (Fin 3)) (h : oldK true u 1=resetForward) :
    sfield.read ((linkStep true hv u v w p ⟨1,k⟩).1.apply u)=0 := by
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      sfield.read ((putK j t).apply x)=sfield.read x := ctl_k (by decide) j t x
  have S (x : BitVec 96) : sfield.read ((putSeal none).apply x)=0 := by
    exact Field.read_assign _ _ _
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  rw [h]
  cases hv <;> cases k <;> simp [effect,ready,parked,resetForward,Patch.compose_apply,K,S]

/-- The same selected mark clears the seal field when RESET0 departs the
center (K1). Neither of the other old lanes can write that initiator seal. -/
theorem reset_clear_seal_pair (hv : Bool) (u v : BitVec 96)
    (h : oldK true u 1=resetForward) :
    (lane 83 4 (by decide)).read (((BStarShort.shortMIS (true,hv) (u,v)).1.apply u))=0 := by
  have O : sfield.read ((MISByteRows.row (true,hv) (u,v)).1.apply u)=0 := by
    rw [←localRow_eq]
    unfold localRow
    dsimp only
    rw [rowPost_left]
    generalize (rowPrefix (true,hv) (u,v)).1 = w
    generalize (rowPrefix (true,hv) (u,v)).2 = p
    cases hv <;> simp only [links,if_true,if_false,Bool.false_eq_true,List.foldl_cons,List.foldl_nil]
    · rw [link_left_read_of_effect sfield (by decide) _ _ _ _ _ ⟨2,some 2⟩
          (seal_effect_frame_noncenter _ _ _ _ _ _ (by decide))]
      exact seal_center_link _ _ _ _ _ _ h
    · rw [link_left_read_of_effect sfield (by decide) _ _ _ _ _ ⟨2,none⟩
          (seal_effect_frame_noncenter _ _ _ _ _ _ (by decide))]
      exact seal_center_link _ _ _ _ _ _ h
  have F : sfield.read (((BStarShort.shortMIS (true,hv) (u,v)).1.apply u)) =
      sfield.read ((MISByteRows.row (true,hv) (u,v)).1.apply u) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [sfield,lane,Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    apply BStarShort.mis_apply_outside
    left
    change 83+i<89
    omega
  exact F.trans O

#print axioms reset_clear_seal_pair

/-- The incoming header door composes the controller over the routed old
pair; the final optional K0 assignment is last. The controller reads old
v and old K0, not that already-patched base. -/
theorem source_door_pair (hu : Bool) (u v : BitVec 96) :
    let out := source v (oldK true v 0)
    ∃ base : BitVec 96,
      (∀ {k : Nat} (f : Field 96 k), 57≤f.offset → f.offset+k≤83 → f.read base=f.read v) ∧
      ((MISByteRows.row (hu,true) (u,v)).2.apply v)=
        (match out.2 with
        | none => out.1.apply base
        | some t => (putK 0 t).apply (out.1.apply base)) := by
  rw [←localRow_eq]
  unfold localRow rowPost
  dsimp only [Prod.fst,Prod.snd,if_true]
  let pr := rowPrefix (hu,true) (u,v)
  let p := (links true).foldl (linkStep hu true u v pr.1) pr.2
  refine ⟨p.2.apply v,?_,?_⟩
  · intro k f lo hi
    exact (ctl_fold f lo hi hu true u v pr.1 pr.2 _ v).2.trans
      (ctl_prefix_right f lo hi hu u v v)
  change (((p.2.compose (source v (oldK true v 0)).1).compose
      (match (source v (oldK true v 0)).2 with | none => .empty _ | some t => putK 0 t)).apply v) = _
  rw [Patch.compose_apply,Patch.compose_apply]
  cases (source v (oldK true v 0)).2
  · change _ &&& BitVec.allOnes 96 ||| 0 = _
    rw [BitVec.and_allOnes]
    exact BitVec.or_zero
  · rfl

#print axioms source_door_pair


/-- If a forward target cannot be supplied by the old non-forward source,
the literal sender lane only undergoes its own fault normalization. -/
theorem parked_incoming_predecessor_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (no : (oldK hu u j).tag≠2)
    (target : (oldK hv v k).tag=2) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=normalizedNoForward hu u j := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have preL := dirty_pre_left hv j pre suf L
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b,p=(a,b) := ⟨p.1,p.2,rfl⟩
  change
    (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  have eq : linkStep hu hv u v pr.1 (a,b) ⟨j,some k⟩=(a,b) := by
    simp [linkStep,ready,no,target]
  rw [H,link,eq,fold_left_frame _ _ _ _ _ _ _ _ _ A]
  have ha := congrArg Prod.fst H
  change p.1=a at ha
  rw [←ha,fold_left_frame _ _ _ _ _ _ _ _ _ preL]
  exact dirty_left_norm hu hv u v j no

/-- The uninterfered-with receiver's own normalization can re-encode a
fault or advance a parked race but does not run the observed supplier. -/
def parkedNeighborBits (h : Bool) (x : BitVec 96) (j : Fin 3) : BitVec 19 :=
  let t := oldK h x j
  if t.fault then encode t else
    if parked t h x j && (t.race==1 || t.race==3) then encode (raceNext t 2)
    else (kField j).read x

private theorem parked_right_norm (hu hv : Bool) (u v : BitVec 96) (j : Fin 3) :
    (kField j).read ((rowPrefix (hu,hv) (u,v)).2.2.apply v)=parkedNeighborBits hv v j := by
  let p := fun k : Fin 3 =>
    let t := oldK hv v k
    if t.fault then putK k t
    else if parked t hv v k && (t.race==1 || t.race==3) then putK k (raceNext t 2)
    else .empty _
  let base := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else ((resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false))
  have fr : Frames j base := by
    dsimp [base]
    split
    · split
      · exact keep_high (by decide) _ _
      · exact empty_frames j
    · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
  have other (k : Fin 3) (N : j≠k) : Frames j (p k) := by
    dsimp only [p]
    split
    · exact fun z=>read_putK_other _ _ N _ z
    · split
      · exact fun z=>read_putK_other _ _ N _ z
      · exact empty_frames j
  have selected (z : BitVec 96) (K : (kField j).read z=(kField j).read v) :
      (kField j).read ((p j).apply z)=parkedNeighborBits hv v j := by
    dsimp only [p,parkedNeighborBits]
    split
    · exact read_putK _ _ _
    · split
      · exact read_putK _ _ _
      · exact (empty_frames j z).trans K
  change (kField j).read ((((base.compose (p 0)).compose (p 1)).compose (p 2)).apply v)=_
  have J := j.isLt
  have H : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
  have js : j=0 ∨ j=1 ∨ j=2 := by
    rcases H with H|H|H
    · exact .inl (Fin.ext H)
    · exact .inr (.inl (Fin.ext H))
    · exact .inr (.inr (Fin.ext H))
  rcases js with rfl|rfl|rfl
  · rw [Patch.compose_apply,other 2 (by decide),Patch.compose_apply,other 1 (by decide),Patch.compose_apply]
    exact selected _ (fr v)
  · rw [Patch.compose_apply,other 2 (by decide),Patch.compose_apply]
    apply selected
    rw [Patch.compose_apply,other 0 (by decide)]
    exact fr v
  · rw [Patch.compose_apply]
    apply selected
    rw [Patch.compose_apply,other 1 (by decide),Patch.compose_apply,other 0 (by decide)]
    exact fr v

/-- An unready forward does not transport on its outgoing mark; the
receiver retains exactly its own normalization, including on approach
to a distinct header. -/
theorem parked_outgoing_successor_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (tag : (oldK hu u j).tag=2)
    (unready : forwardReady hu u j=false) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=parkedNeighborBits hv v k := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have preR := dirty_pre_right hv j k pre suf L link
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k link)
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  have W : ready hu u j (oldK hu u j)=false := unready
  have idle : linkStep hu hv u v pr.1 p ⟨j,some k⟩=p := by
    rcases p with ⟨a,b⟩
    simp [linkStep,W,tag]
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [link,idle,fold_right_frame _ _ _ _ _ _ _ _ _ (Z k link),
    fold_right_frame _ _ _ _ _ _ _ _ _ preR]
  exact parked_right_norm hu hv u v k

#print axioms parked_incoming_predecessor_pair
#print axioms parked_outgoing_successor_pair

/-- A normalized neighbor at a different slot may change race but never
changes its wire class. -/
theorem parkedNeighborBits_tag (h g : Bool) (x : BitVec 96) (j : Fin 3) :
    (decode g (parkedNeighborBits h x j)).tag=(oldK h x j).tag := by
  unfold parkedNeighborBits
  dsimp only
  split
  · exact ShortPacketTag.encode_decoded_tag _ _ _
  · split
    · rename_i HH
      let t := oldK h x j
      have C : parked t h x j=true ∧ (t.race==1 || t.race==3)=true := Bool.and_eq_true_iff.mp HH
      have F : t.tag=2 := by
        have X := C.1
        unfold parked at X
        simp only [Bool.and_eq_true,beq_iff_eq] at X
        exact X.1.1.1
      have casesR : t.race=1 ∨ t.race=3 := by
        have X := C.2
        simpa only [Bool.or_eq_true,beq_iff_eq] using X
      obtain ⟨O,R,A,P⟩ := ShortPacketTag.decoded_forward_bounds (atGate h x j) ((kField j).read x) F
      change t.opcode<8 at O
      change t.outcome=0 at A
      change t.payload<128 at P
      change (decode g (encode (raceNext t 2))).tag=t.tag
      have out : ∃ r : Nat, r<8 ∧ raceNext t 2={t with race:=r} := by
        rcases casesR with E|E
        · exact ⟨2,by decide,by simp [raceNext,E]⟩
        · exact ⟨5,by decide,by simp [raceNext,E]⟩
      obtain ⟨r,rb,eq⟩ := out
      rw [eq]
      apply ShortPacketTag.inherited_encode_tag
      · exact ShortPacketTag.forward_low_bound _ O rb A (by change t.payload<256; omega)
      · change t.tag<4
        omega
    · exact ShortPacketTag.no_kind_change _ _ _

/-- At a non-gate successor there is no independent race observation. -/
theorem parkedNeighborBits_ungated (h : Bool) (x : BitVec 96) (j : Fin 3)
    (gate : atGate h x j=false) :
    parkedNeighborBits h x j=normalizedNoForward h x j := by
  simp [parkedNeighborBits,normalizedNoForward,parked,gate]

theorem normalizedNoForward_tag (h g : Bool) (x : BitVec 96) (j : Fin 3) :
    (decode g (normalizedNoForward h x j)).tag=(oldK h x j).tag := by
  unfold normalizedNoForward
  dsimp only
  split
  · exact ShortPacketTag.encode_decoded_tag _ _ _
  · exact ShortPacketTag.no_kind_change _ _ _

#print axioms parkedNeighborBits_tag
#print axioms parkedNeighborBits_ungated
#print axioms normalizedNoForward_tag

/-- Faulted or ungated inherited forward tokens are ready to drain.
A held forward decodes only as a real, live ADMIT in race 1, 2 or 3. -/
theorem unready_forward_shape (h : Bool) (x : BitVec 96) (j : Fin 3)
    (tag : (oldK h x j).tag=2) (hold : forwardReady h x j=false) :
    let t := oldK h x j
    (t.opcode=2 ∧ t.fault=false ∧ atGate h x j=true) ∧
    (t.race=1 ∨ t.race=2 ∨ t.race=3) ∧
    (t.payload≤1 ∧ t.outcome=0 ∧ t.applied=false) := by
  dsimp only
  let t := oldK h x j
  have p : parked t h x j=true ∧ t.race<4 := by
    simpa [forwardReady, ready, ←show oldK h x j=t from rfl,tag] using hold
  have G : (t.opcode=2 ∧ t.fault=false ∧ atGate h x j=true) := by
    have P := p.1
    simp only [parked, show t.tag=2 from tag, beq_self_eq_true, Bool.true_and,
      Bool.and_eq_true_iff, beq_iff_eq] at P
    exact ⟨P.1.2,by
      have Q := P.1.1
      exact Bool.eq_false_iff.mpr (fun H=>by rw [H] at Q; contradiction),P.2⟩
  have D : t=decode true ((kField j).read x) := by
    unfold t oldK
    rw [G.2.2]
  have V := ShortPacketTag.gate_admit_shape ((kField j).read x)
    (by rw [←D]; exact tag) (by rw [←D]; exact G.1) (by rw [←D]; exact G.2.1)
  rw [←D] at V
  have R : t.race=1 ∨ t.race=2 ∨ t.race=3 := by have := p.2; have := V.1; omega
  exact ⟨G,R,V.2.2⟩

#print axioms unready_forward_shape

/-- The responder header's K0 is excluded from every ordinary link.
Its own source alone supplies an optional K0 assignment; absent that
assignment, only normalization of its own old bytes is possible. -/
theorem source_door_k0_pair (hu : Bool) (u v : BitVec 96) :
    let out := source v (oldK true v 0)
    (kField 0).read ((MISByteRows.row (hu,true) (u,v)).2.apply v)=
      match out.2 with
      | none => normalizedNoForward true v 0
      | some t => encode t := by
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  let pr := rowPrefix (hu,true) (u,v)
  let p := (links true).foldl (linkStep hu true u v pr.1) pr.2
  change (kField 0).read ((rowPost true v p).2.apply v)=_
  cases E : (source v (oldK true v 0)).2 with
  | some t =>
    unfold rowPost
    simp only [if_true,E,Patch.compose_apply]
    exact read_putK _ _ _
  | none =>
    rw [post_frame true v p 0 (.inr (.inr E))]
    have nd : ∀ l∈links true, some (0 : Fin 3)≠l.dst := by
      intro l M
      simp [links] at M
      rcases M with rfl|rfl|rfl <;> decide
    unfold p
    rw [fold_right_frame _ _ _ _ _ _ _ _ _ nd]
    let q := fun k : Fin 3 =>
      let t := oldK true v k
      if t.fault then putK k t
      else if parked t true v k && (t.race==1 || t.race==3) then putK k (raceNext t 2)
      else .empty _
    let base := if grant v 1 && (grant v 0 || grant v 2) then
        grantsPatch (canonical v) else .empty _
    change (kField 0).read ((((base.compose (q 0)).compose (q 1)).compose (q 2)).apply v)=_
    apply dirty_three_normalizers
    · simp [q,parked,atGate]
    · dsimp [base]
      split
      · exact keep_high (by decide) _ _
      · exact empty_frames _
    · intro j J
      dsimp only [q]
      split
      · exact fun z=>read_putK_other _ _ J _ z
      · split
        · exact fun z=>read_putK_other _ _ J _ z
        · exact empty_frames _

#print axioms source_door_k0_pair
/-- The old immutable MIS1 header view used by the support wrapper. -/
def headerGrantView (u : BitVec 96) :=
  BStarShort.grantView 89 3 true u (oldK true u)

private theorem grant_bits (f : Fin 3 → Bool) (u : BitVec 96) (j : Fin 3) :
    ((grantsPatch f).apply u).getLsbD (91-j.val) = f j := by
  have kl : 2-j.val<3 := by have := j.isLt; omega
  have IX : 89+(2-j.val)=91-j.val := by have := j.isLt; omega
  have E : (gfield.read ((grantsPatch f).apply u)).getLsbD (2-j.val) = f j := by
    change ((lane 89 3 (by decide)).read ((lane 89 3 (by decide)).assign
      (BitVec.ofNat 3 (4*(f 0).toNat+2*(f 1).toNat+(f 2).toNat)) |>.apply u)).getLsbD _ = _
    rw [Field.read_assign]
    match j with
    | ⟨0,_⟩ =>
      change (BitVec.ofNat 3 (4*(f 0).toNat+2*(f 1).toNat+(f 2).toNat)).getLsbD 2=f 0
      cases f 0 <;> cases f 1 <;> cases f 2 <;> rfl
    | ⟨1,_⟩ =>
      change (BitVec.ofNat 3 (4*(f 0).toNat+2*(f 1).toNat+(f 2).toNat)).getLsbD 1=f 1
      cases f 0 <;> cases f 1 <;> cases f 2 <;> rfl
    | ⟨2,_⟩ =>
      change (BitVec.ofNat 3 (4*(f 0).toNat+2*(f 1).toNat+(f 2).toNat)).getLsbD 0=f 2
      cases f 0 <;> cases f 1 <;> cases f 2 <;> rfl
  unfold gfield Field.read at E
  simpa only [lane,BitVec.getLsbD_extractLsb',kl,decide_true,Bool.true_and,IX] using E

private theorem dep_eq (u : BitVec 96) (j : Fin 3) (op : Nat) (O : op≠2) :
    (ready true u j (oldK true u j) && !(oldK true u j).fault &&
      (oldK true u j).opcode==op) =
      ((oldK true u j).tag==2 && !(oldK true u j).fault && (oldK true u j).opcode==op) := by
  by_cases E : (oldK true u j).opcode=op
  · have K : (oldK true u j).opcode≠2 := by omega
    have N : ((oldK true u j).opcode==2)=false :=
      Bool.eq_false_iff.mpr (fun H=>K (beq_iff_eq.mp H))
    simp only [ready,parked,N,Bool.and_false,Bool.false_and,Bool.not_false,Bool.and_true]
  · have N : ((oldK true u j).opcode==op)=false :=
      Bool.eq_false_iff.mpr (fun H=>E (beq_iff_eq.mp H))
    simp only [N,Bool.and_false]

private theorem grant_prefix_header_value (hv : Bool) (u v : BitVec 96) (j : Fin 3) :
    (gfield.read ((rowPrefix (true,hv) (u,v)).2.1.apply u)).getLsbD (2-j.val) =
      (headerGrantView u).nextValue j := by
  have shape (k : Fin 3) : canonical u k=(headerGrantView u).canonical k := rfl
  have norm (k : Fin 3) (t q : Token) (b : Bool) (x : BitVec 96) :=
    ctl_norm gfield (by decide) k t q b x
  unfold rowPrefix
  dsimp only
  simp only [if_true,Bool.true_and,Patch.compose_apply,norm,dep_eq u _ 0 (by decide),dep_eq u _ 3 (by decide)]
  let g := headerGrantView u
  have m : (gfield.read ((grantsPatch fun k=>g.nextValue k).apply u)).getLsbD (2-j.val) =
      g.nextValue j := by
    have I : 89+(2-j.val)=91-j.val := by have := j.isLt; omega
    have K : 2-j.val<3 := by have := j.isLt; omega
    simpa only [gfield,Field.read,lane,BitVec.getLsbD_extractLsb',K,decide_true,Bool.true_and,I] using
      grant_bits g.nextValue u j
  refine Eq.trans ?_ m
  apply congrArg (fun f : Fin 3→Bool => (gfield.read ((grantsPatch f).apply u)).getLsbD (2-j.val))
  funext k
  change _ = (headerGrantView u).nextValue k
  simp only [shape]
  simp only [BStarShort.GrantView.nextValue,BStarShort.GrantView.win,BStarShort.GrantView.centerWin]
  have H : (headerGrantView u).header=true := rfl
  simp only [H,if_true]
  have A (j : Fin 3) : (headerGrantView u).ask j =
      ((oldK true u j).tag==2 && !(oldK true u j).fault && (oldK true u j).opcode==3) := rfl
  have R (j : Fin 3) : (headerGrantView u).release j =
      ((oldK true u j).tag==2 && !(oldK true u j).fault && (oldK true u j).opcode==0) := rfl
  simp only [A,R]
  by_cases K : k=1 <;> simp [K,Bool.and_left_comm,Bool.and_assoc,Bool.and_comm]

/-- Exact work-row left grant equation, prior to support erasure. -/
theorem grant_left_row (hv : Bool) (u v : BitVec 96) (j : Fin 3) :
    ((MISByteRows.row (true,hv) (u,v)).1.apply u).getLsbD (91-j.val)=
      (headerGrantView u).nextValue j := by
  have O : ((gfield.read ((MISByteRows.row (true,hv) (u,v)).1.apply u)).getLsbD
      (2-j.val))=(headerGrantView u).nextValue j := by
    rw [←localRow_eq]
    unfold localRow
    dsimp only
    rw [rowPost_left,grant_fold_left]
    exact grant_prefix_header_value hv u v j
  have I : 89+(2-j.val)=91-j.val := by have := j.isLt; omega
  have K : 2-j.val<3 := by have := j.isLt; omega
  simpa only [gfield,Field.read,lane,BitVec.getLsbD_extractLsb',K,decide_true,Bool.true_and,I] using O

/-- Exact shortMIS initiator equation, including preserved bits whose
value agrees due to the structural support correction. -/
theorem grant_left_short (hv : Bool) (u v : BitVec 96) (j : Fin 3) :
    ((BStarShort.shortMIS (true,hv) (u,v)).1.apply u).getLsbD (91-j.val)=
      (headerGrantView u).nextValue j := by
  let g := headerGrantView u
  let i := 91-j.val
  have M : (BStarShort.grantErase (w:=96) 89 g).getLsbD i=g.drop j := by
    rw [BStarShort.grantErase_mask]
    have J : j=0 ∨ j=1 ∨ j=2 := by
      have L := j.isLt
      rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with A|A|A
      · exact Or.inl (Fin.ext A)
      · exact Or.inr (Or.inl (Fin.ext A))
      · exact Or.inr (Or.inr (Fin.ext A))
    rcases J with rfl|rfl|rfl <;> simp [i]
  have K := BStarShort.shortMIS_mask (true,hv) (u,v) i
  change _ = (((MISByteRows.row (true,hv) (u,v)).1.mask.getLsbD i) &&
    !(BStarShort.grantErase (w:=96) 89 g).getLsbD i) at K
  rw [M] at K
  cases D : g.drop j
  · simp only [D,Bool.not_false,Bool.and_true] at K
    cases R : (MISByteRows.row (true,hv) (u,v)).1.mask.getLsbD i
    · exact (Patch.hold _ _ _ (K.trans R)).trans
        ((Patch.hold _ _ _ R).symm.trans (grant_left_row hv u v j))
    · refine (Patch.write _ _ _ (K.trans R)).trans ?_
      exact (Patch.write _ _ _ R).symm.trans (grant_left_row hv u v j)
  · simp only [D,Bool.not_true,Bool.and_false] at K
    exact (Patch.hold _ _ _ K).trans (BStarShort.GrantView.drop_holds g j D).symm

#print axioms grant_left_short

private theorem right_grant_effect (u v : BitVec 96) (hu : Bool) (l : Link) (w : Bool) (t : Token) :
    ControllerFrame gfield (effect u v hu true l.src l.dst w t).2.1 := by
  unfold effect
  dsimp only
  split
  · exact ctl_empty _
  split
  · split
    · exact ctl_compose (ctl_put _ _ _ _ (.inl (by decide))) (ctl_put _ _ _ _ (.inr (by decide)))
    · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · split
    · exact ctl_empty _
    · split <;> exact ctl_empty _
  · exact ctl_empty _

private theorem right_grant_link (hu : Bool) (u v : BitVec 96) (w : Fin 3→Bool)
    (p : Pair (Patch 96)) (l : Link) :
    gfield.read ((linkStep hu true u v w p l).2.apply v)=gfield.read (p.2.apply v) := by
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      gfield.read ((putK j t).apply x)=gfield.read x := ctl_k (by decide) j t x
  have G (x : BitVec 96) := right_grant_effect u v hu l (w l.src) (oldK hu u l.src) x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · split <;> simp only [Patch.compose_apply,K,G]
  · split
    · rfl
    · split
      · rfl
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> rfl

private theorem right_grant_fold (hu : Bool) (u v : BitVec 96) (w : Fin 3→Bool)
    (p : Pair (Patch 96)) (L : List Link) :
    gfield.read ((L.foldl (linkStep hu true u v w) p).2.apply v)=gfield.read (p.2.apply v) := by
  induction L generalizing p with
  | nil => rfl
  | cons l tail ih => exact (ih _).trans (right_grant_link hu u v w p l)

private theorem right_grant_source (v : BitVec 96) (t : Token) :
    ControllerFrame gfield (source v t).1 := by
  have H (o w : Nat) (ol : o+w≤89) (h : o+w≤96) (a : Nat) :
      ControllerFrame gfield (put o w h a) := ctl_put _ _ _ _ (.inr ol)
  unfold source
  dsimp only
  split
  · exact H _ _ (by decide) _ _
  split
  · apply ctl_compose
    · split
      · exact H _ _ (by decide) _ _
      · exact ctl_empty _
    · exact H _ _ (by decide) _ _
  split
  · exact ctl_empty _
  split
  · exact H _ _ (by decide) _ _
  split
  · exact H _ _ (by decide) _ _
  · exact H _ _ (by decide) _ _
  · split <;> exact H _ _ (by decide) _ _
  · exact ctl_compose (ctl_compose (H _ _ (by decide) _ _) (H _ _ (by decide) _ _))
      (H _ _ (by decide) _ _)
  · exact H _ _ (by decide) _ _
  · exact H _ _ (by decide) _ _
  · exact H _ _ (by decide) _ _

/-- Exact right header normalization: overlapping readers are cleared
if a writer is present. No old-initiator flags are consulted. -/
theorem grant_right_short (hu : Bool) (u v : BitVec 96) (j : Fin 3) :
    ((BStarShort.shortMIS (hu,true) (u,v)).2.apply v).getLsbD (91-j.val)=
      (headerGrantView v).canonical j := by
  have I : 89+(2-j.val)=91-j.val := by have := j.isLt; omega
  have K : 2-j.val<3 := by have := j.isLt; omega
  suffices O : (gfield.read ((MISByteRows.row (hu,true) (u,v)).2.apply v)).getLsbD (2-j.val)
      = (headerGrantView v).canonical j by
    simpa only [gfield,Field.read,lane,BitVec.getLsbD_extractLsb',K,decide_true,Bool.true_and,I,
      BStarShort.shortMIS_responder] using O
  rw [←localRow_eq]
  unfold localRow rowPost
  dsimp only [Prod.fst,Prod.snd,if_true]
  simp only [if_true]
  rw [Patch.compose_apply,Patch.compose_apply]
  have F : ControllerFrame gfield
      (match (source v (oldK true v 0)).2 with | none=>.empty 96 | some t=>putK 0 t) := by
    split
    · exact ctl_empty _
    · exact ctl_k (by decide) _ _
  rw [F,right_grant_source,right_grant_fold]
  have norm (k : Fin 3) (t q : Token) (b : Bool) (x : BitVec 96) :=
    ctl_norm gfield (by decide) k t q b x
  unfold rowPrefix
  dsimp only
  simp only [if_true,Patch.compose_apply,norm]
  change (gfield.read ((if grant v 1 && (grant v 0 || grant v 2)
    then grantsPatch (canonical v) else Patch.empty 96).apply v)).getLsbD (2-j.val) = _
  have H : canonical v j = (headerGrantView v).canonical j := rfl
  split
  · have Y := grant_bits (canonical v) v j
    rw [←H]
    simpa only [gfield,Field.read,lane,BitVec.getLsbD_extractLsb',K,decide_true,Bool.true_and,I] using Y
  · rename_i C
    rw [ctl_empty gfield v,←H]
    have R : (gfield.read v).getLsbD (2-j.val)=grant v j := by
      simp only [gfield,Field.read,lane,grant,BitVec.getLsbD_extractLsb',K,decide_true,Bool.true_and,I]
    rw [R]
    cases W : grant v 1
    · simp [canonical,W]
    · have B : grant v 0=false ∧ grant v 2=false := by simpa [W] using C
      have J : j=0 ∨ j=1 ∨ j=2 := by
        have L := j.isLt
        rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with A|A|A
        · exact Or.inl (Fin.ext A)
        · exact Or.inr (Or.inl (Fin.ext A))
        · exact Or.inr (Or.inr (Fin.ext A))
      rcases J with rfl|rfl|rfl <;> simp [canonical,W,B.1,B.2]

#print axioms grant_right_short

set_option maxHeartbeats 350000
/-- Only the bank or selector fields, not grant bits or the seal. -/
def ReaderWindow {w : Nat} (f : Field 96 w) : Prop :=
  (87≤f.offset ∧ f.offset+w≤89) ∨ (92≤f.offset ∧ f.offset+w≤93)

private theorem reader_effect_frame {w : Nat} (f : Field 96 w)
    (W : ReaderWindow f) (u v : BitVec 96) (hu hv : Bool) (l : Link)
    (win : Bool) (t : Token) :
    (grant u 1=false → ControllerFrame f (effect u v hu hv l.src l.dst win t).1) ∧
    (grant v 1=false → ControllerFrame f (effect u v hu hv l.src l.dst win t).2.1) := by
  have lo : 87≤f.offset := by rcases W with H|H <;> omega
  have S (d : Option Nat) : ControllerFrame f (putSeal d) :=
    ctl_put _ _ _ _ (.inr lo)
  unfold effect
  dsimp only
  split
  · exact ⟨fun _=>ctl_empty f,fun _=>ctl_empty f⟩
  split
  · constructor
    · intro _
      split <;> exact ctl_empty f
    · intro G
      simp only [G,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]; exact ctl_empty f
  split
  · exact ⟨fun _=>ctl_empty f,fun _=>ctl_empty f⟩
  split
  · exact ⟨fun _=>S none,fun _=>ctl_empty f⟩
  split
  · exact ⟨fun _=>ctl_empty f,fun _=>ctl_empty f⟩
  split
  · constructor
    · intro G
      simp only [G,Bool.false_and,Bool.not_false]; exact ctl_empty f
    · intro _
      split
      · exact ctl_empty f
      · split <;> exact ctl_empty f
  · exact ⟨fun _=>ctl_empty f,fun _=>ctl_empty f⟩

private theorem reader_grants {w : Nat} (f : Field 96 w) (W : ReaderWindow f)
    (g : Fin 3→Bool) : ControllerFrame f (grantsPatch g) := by
  apply ctl_put
  rcases W with H|H
  · exact .inl H.2
  · exact .inr H.1

private theorem reader_prefix_frame {w : Nat} (f : Field 96 w) (W : ReaderWindow f)
    (hu hv : Bool) (u v : BitVec 96) :
    (hu=true → ControllerFrame f (rowPrefix (hu,hv) (u,v)).2.1) ∧
    (hv=true → ControllerFrame f (rowPrefix (hu,hv) (u,v)).2.2) := by
  have low : 57≤f.offset := by rcases W with H|H <;> omega
  constructor
  · intro H
    subst hu
    unfold rowPrefix
    dsimp only
    simp only [if_true]
    exact ctl_compose (ctl_compose (ctl_compose (reader_grants f W _)
      (ctl_norm f low 0 _ _ _)) (ctl_norm f low 1 _ _ _)) (ctl_norm f low 2 _ _ _)
  · intro H
    subst hv
    have P (b : Bool) : ControllerFrame f
        (if b then grantsPatch (canonical v) else Patch.empty 96) := by
      cases b
      · exact ctl_empty f
      · exact reader_grants f W _
    unfold rowPrefix
    dsimp only
    simp only [if_true]
    exact ctl_compose (ctl_compose (ctl_compose (P _)
      (ctl_norm f low 0 _ _ _)) (ctl_norm f low 1 _ _ _)) (ctl_norm f low 2 _ _ _)

private theorem reader_source_frame {w : Nat} (f : Field 96 w) (W : ReaderWindow f)
    (v : BitVec 96) (t : Token) : ControllerFrame f (source v t).1 := by
  have lo : 87≤f.offset := by rcases W with H|H <;> omega
  have r : ControllerFrame f resetSource := ctl_put 57 26 (by decide) _ (.inr (by omega))
  have p (i j : Nat) : ControllerFrame f (phaseOp i j) :=
    ctl_put _ _ _ _ (.inr (by omega))
  unfold source
  dsimp only
  split
  · exact r
  split
  · apply ctl_compose
    · split <;> first | exact r | exact ctl_empty f
    · exact ctl_put _ _ _ _ (.inr (by omega))
  split
  · exact ctl_empty f
  split
  · exact r
  split
  · exact p 1 1
  · exact p 1 2
  · split
    · exact p 1 3
    · exact r
  · exact ctl_compose (ctl_compose (p 1 4)
      (ctl_put 72 6 (by decide) t.payload (.inr (by omega))))
      (ctl_put 68 4 (by decide) 0 (.inr (by omega)))
  · exact p 1 5
  · exact p 1 6
  · exact r
private theorem reader_link {w : Nat} (f : Field 96 w)
    (W : ReaderWindow f)
    (hu hv : Bool) (u v : BitVec 96) (win : Fin 3→Bool) (p : Pair (Patch 96))
    (l : Link) (X : BitVec 96) :
    (grant u 1=false → f.read ((linkStep hu hv u v win p l).1.apply X)=f.read (p.1.apply X)) ∧
    (grant v 1=false → f.read ((linkStep hu hv u v win p l).2.apply X)=f.read (p.2.apply X)) := by
  have low : 57≤f.offset := by rcases W with H|H <;> omega
  have F := reader_effect_frame f W u v hu hv l (win l.src) (oldK hu u l.src)
  have K (j : Fin 3) (t : Token) (z : BitVec 96) :
      f.read ((putK j t).apply z)=f.read z := ctl_k low j t z
  have FL (h : grant u 1=false) (z : BitVec 96) := F.1 h z
  have FR (h : grant v 1=false) (z : BitVec 96) := F.2 h z
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · split <;> (constructor <;> intro no)
    · simp only [Patch.compose_apply,K,FL no]
    · simp only [Patch.compose_apply,FR no]
    · simp only [Patch.compose_apply,K,FL no]
    · simp only [Patch.compose_apply,K,FR no]
  · split
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · split
      · split <;> (constructor <;> intro no <;> first | rfl | simp only [Patch.compose_apply,K])
      · split
        · constructor <;> intro _ <;> simp only [Patch.compose_apply,K]
        · split <;> (constructor <;> intro no <;> first | rfl | simp only [Patch.compose_apply,K])

private theorem reader_fold {w : Nat} (f : Field 96 w)
    (W : ReaderWindow f)
    (hu hv : Bool) (u v : BitVec 96) (win : Fin 3→Bool) (p : Pair (Patch 96))
    (L : List Link) (X : BitVec 96) :
    (grant u 1=false → f.read ((L.foldl (linkStep hu hv u v win) p).1.apply X)=f.read (p.1.apply X)) ∧
    (grant v 1=false → f.read ((L.foldl (linkStep hu hv u v win) p).2.apply X)=f.read (p.2.apply X)) := by
  induction L generalizing p with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons l L ih =>
    have H := ih (linkStep hu hv u v win p l)
    have T := reader_link f W hu hv u v win p l X
    exact ⟨fun A=>(H.1 A).trans (T.1 A),fun B=>(H.2 B).trans (T.2 B)⟩


/-- Old no-writer implies bank and selector retention on the complete
initiator row, regardless of the other endpoint or its token lanes. -/
theorem reader_outgoing_pair {w : Nat} (f : Field 96 w) (W : ReaderWindow f)
    (hv : Bool) (u v : BitVec 96) (no : u.getLsbD 90=false) :
    f.read (((MISByteRows.row (true,hv) (u,v)).1).apply u)=f.read u := by
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [rowPost_left]
  exact ((reader_fold f W true hv u v _ _ _ u).1 no).trans
    ((reader_prefix_frame f W true hv u v).1 rfl u)

/-- The corresponding no-writer property on a marked old responder.
In particular neither incoming COMMIT nor any source-door outcome
can replace its reference bank or selector. -/
theorem reader_incoming_pair {w : Nat} (f : Field 96 w) (W : ReaderWindow f)
    (hu : Bool) (u v : BitVec 96) (no : v.getLsbD 90=false) :
    f.read (((MISByteRows.row (hu,true) (u,v)).2).apply v)=f.read v := by
  rw [←localRow_eq]
  unfold localRow rowPost
  dsimp only
  simp only [if_true,Patch.compose_apply]
  generalize Hr : ((links true).foldl (linkStep hu true u v (rowPrefix (hu,true) (u,v)).1)
    (rowPrefix (hu,true) (u,v)).2).2.apply v = r
  have low : 57≤f.offset := by rcases W with H|H <;> omega
  have H : f.read r=f.read v := by
    rw [←Hr]
    exact ((reader_fold f W hu true u v _ _ _ v).2 no).trans
      ((reader_prefix_frame f W hu true u v).2 rfl v)
  have S := reader_source_frame f W v (oldK true v 0) r
  split
  · rw [ctl_empty f _,S,H]
  · rw [ctl_k low _ _ _,S,H]

#print axioms reader_outgoing_pair
#print axioms reader_incoming_pair

set_option maxHeartbeats 150000
private def msf : Field 96 1 := lane 92 1 (by decide)

/-- Literal old-pair guard for the short right-header selector write. -/
def selectorGuard (hu : Bool) (u v : BitVec 96) : Prop :=
  let t := oldK hu u 0
  t.tag = 2 ∧ t.fault=false ∧ t.opcode=6 ∧ t.applied=false ∧
    v.getLsbD 90=true ∧ get v 92 1 (by decide)=t.payload/4 ∧
    readSeal v=some t.payload ∧
    v.getLsbD (88-(t.payload/2)%2)=(t.payload%2==1)

private theorem msf_reset : ControllerFrame msf resetSource :=
  ctl_put 57 26 (by decide) _ (.inr (by decide))
private theorem msf_phase (op : Nat) : ControllerFrame msf (phaseOp 1 op) :=
  ctl_put 78 5 (by decide) _ (.inr (by decide))
private theorem msf_seal (d : Option Nat) : ControllerFrame msf (putSeal d) :=
  ctl_put 83 4 (by decide) _ (.inr (by decide))
private theorem msf_grant (g : Fin 3→Bool) : ControllerFrame msf (grantsPatch g) :=
  ctl_put 89 3 (by decide) _ (.inr (by decide))
private theorem msf_norm {c : Bool} (t q : Token) (j : Fin 3) :
    ControllerFrame msf (if t.fault then putK j t else if c then putK j q else Patch.empty 96) :=
  ctl_norm msf (by decide) j t q c

private theorem msf_source (v : BitVec 96) (t : Token) :
    ControllerFrame msf (source v t).1 := by
  unfold source
  dsimp only
  split
  · exact msf_reset
  split
  · refine ctl_compose ?_ (ctl_put 81 2 (by decide) 2 (.inr (by decide)))
    split
    · exact msf_reset
    · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact msf_reset
  split
  · exact msf_phase _
  · exact msf_phase _
  · split
    · exact msf_phase _
    · exact msf_reset
  · exact ctl_compose
      (ctl_compose (msf_phase _) (ctl_put 72 6 (by decide) _ (.inr (by decide))))
      (ctl_put 68 4 (by decide) _ (.inr (by decide)))
  · exact msf_phase _
  · exact msf_phase _
  · exact msf_reset

private theorem msf_effect_left (u v : BitVec 96) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (w : Bool) (t : Token) :
    ControllerFrame msf (effect u v hu hv j k w t).1 := by
  unfold effect
  dsimp only
  split
  · exact ctl_empty _
  split
  · split <;> exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact msf_seal none
  split
  · exact ctl_empty _
  split
  · split
    · exact ctl_empty _
    · split
      · exact ctl_put (88-(t.payload/2)%2) 1 (by omega) _ (.inr (by change 88-(t.payload/2)%2+1≤92; omega))
      · exact msf_seal (some t.payload)
  · exact ctl_empty _

private theorem msf_effect_right (u v : BitVec 96) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (w : Bool) (t : Token)
    (H : t.tag=2 → t.fault=false → t.opcode=6 → hv=true → j=0 →
      k=some 1 → t.applied=false → v.getLsbD 90=true →
      get v 92 1 (by decide)=t.payload/4 → readSeal v=some t.payload →
      v.getLsbD (88-(t.payload/2)%2)=(t.payload%2==1) → False)
    (tag : t.tag=2) :
    ControllerFrame msf (effect u v hu hv j k w t).2.1 := by
  unfold effect
  dsimp only
  split
  · exact ctl_empty _
  · rename_i F
    have hf : t.fault=false := Bool.eq_false_iff.mpr F
    split
    · rename_i C
      simp only [Bool.and_eq_true, beq_iff_eq] at C
      obtain ⟨⟨⟨o,h⟩,j0⟩,k1⟩ := C
      split
      · rename_i G
        change ((!t.applied && v.getLsbD 90 && get v 92 1 (by decide)==t.payload/4 &&
          readSeal v==some t.payload && (v.getLsbD (88-(t.payload/2)%2)==(t.payload%2==1)))=true) at G
        simp only [Bool.and_eq_true, beq_iff_eq] at G
        obtain ⟨⟨⟨⟨a,b⟩,c⟩,d⟩,e⟩ := G
        have ap : t.applied=false := by cases t.applied <;> simp_all
        exact (H tag hf o h j0 k1 ap b c d e).elim
      · exact ctl_empty _
    · split
      · exact ctl_empty _
      · split
        · exact ctl_empty _
        · split
          · exact ctl_empty _
          · split
            · split
              · exact ctl_empty _
              · split <;> exact ctl_empty _
            · exact ctl_empty _

private theorem msf_prefix_left (hu hv : Bool) (u v : BitVec 96) :
    ControllerFrame msf (rowPrefix (hu,hv) (u,v)).2.1 := by
  unfold rowPrefix
  dsimp only
  refine ctl_compose (ctl_compose (ctl_compose ?_ (msf_norm _ _ _)) (msf_norm _ _ _)) (msf_norm _ _ _)
  split
  · exact msf_grant _
  · exact ctl_compose (ctl_compose msf_reset (msf_seal _)) (msf_grant _)

private theorem msf_prefix_right (hu hv : Bool) (u v : BitVec 96) :
    ControllerFrame msf (rowPrefix (hu,hv) (u,v)).2.2 := by
  unfold rowPrefix
  dsimp only
  refine ctl_compose (ctl_compose (ctl_compose ?_ (msf_norm _ _ _)) (msf_norm _ _ _)) (msf_norm _ _ _)
  split
  · split
    · exact msf_grant _
    · exact ctl_empty _
  · exact ctl_compose (ctl_compose msf_reset (msf_seal _)) (msf_grant _)

private theorem msf_ready_tag (u : BitVec 96) (hu : Bool) (j : Fin 3) (t : Token)
    (E : ready hu u j t=true) : t.tag=2 := by
  have Q := (Bool.and_eq_true_iff.mp E).1
  exact beq_iff_eq.mp Q

private theorem msf_link_left (hu hv : Bool) (u v : BitVec 96)
    (w : Fin 3→Bool) (p : Pair (Patch 96)) (l : Link) :
    msf.read ((linkStep hu hv u v w p l).1.apply u)=msf.read (p.1.apply u) := by
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      msf.read ((putK j t).apply x)=msf.read x := ctl_k (by decide) j t x
  have H (x : BitVec 96) := msf_effect_left u v hu hv l.src l.dst (w l.src) (oldK hu u l.src) x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · split <;> simp only [Patch.compose_apply,K,H]
  · split
    · rfl
    · split
      · split <;> first | rfl | simp only [Patch.compose_apply,K]
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> first | rfl | simp only [Patch.compose_apply,K]

private theorem msf_link_right (hu hv : Bool) (u v : BitVec 96)
    (w : Fin 3→Bool) (p : Pair (Patch 96)) (l : Link) (G : ¬selectorGuard hu u v) :
    msf.read ((linkStep hu hv u v w p l).2.apply v)=msf.read (p.2.apply v) := by
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      msf.read ((putK j t).apply x)=msf.read x := ctl_k (by decide) j t x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · rename_i R
    have H : ControllerFrame msf (effect u v hu hv l.src l.dst (w l.src) (oldK hu u l.src)).2.1 := by
      apply msf_effect_right
      · intro tag hf op _ j0 _ appl writer sel hs banked
        apply G
        change (oldK hu u 0).tag = 2 ∧ _
        simpa only [j0] using And.intro tag (And.intro hf (And.intro op (And.intro appl (And.intro writer (And.intro sel (And.intro hs banked))))))
      · exact msf_ready_tag _ _ _ _ R
    have E (x : BitVec 96) := H x
    split <;> simp only [Patch.compose_apply,K,E]
  · split
    · rfl
    · split
      · split <;> rfl
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> rfl

private theorem msf_post_right (hu : Bool) (v : BitVec 96) (p : Pair (Patch 96)) :
    msf.read ((rowPost hu v p).2.apply v)=msf.read (p.2.apply v) := by
  have K (t : Token) (x : BitVec 96) :
      msf.read ((putK 0 t).apply x)=msf.read x := ctl_k (by decide) 0 t x
  unfold rowPost
  split
  · dsimp only
    rw [Patch.compose_apply,Patch.compose_apply]
    split
    · rw [ctl_empty msf,msf_source]
    · rw [K,msf_source]
  · rfl

theorem selector_left_pair (hu hv : Bool) (u v : BitVec 96) :
    ((MISByteRows.row (hu,hv) (u,v)).1.apply u).getLsbD 92=u.getLsbD 92 := by
  rw [←localRow_eq]
  have H (w : Fin 3→Bool) (p : Pair (Patch 96)) (L : List Link) :
      msf.read ((L.foldl (linkStep hu hv u v w) p).1.apply u)=msf.read (p.1.apply u) := by
    induction L generalizing p with
    | nil => rfl
    | cons l t IH => exact (IH _).trans (msf_link_left hu hv u v w p l)
  have E := H (rowPrefix (hu,hv) (u,v)).1 (rowPrefix (hu,hv) (u,v)).2 (links hv)
  have F := E.trans (msf_prefix_left hu hv u v u)
  have P : (rowPost hv v ((links hv).foldl (linkStep hu hv u v
      (rowPrefix (hu,hv) (u,v)).1) (rowPrefix (hu,hv) (u,v)).2)).1=
      ((links hv).foldl (linkStep hu hv u v (rowPrefix (hu,hv) (u,v)).1)
        (rowPrefix (hu,hv) (u,v)).2).1 := by unfold rowPost; split <;> rfl
  have Q : msf.read ((localRow (hu,hv) (u,v)).1.apply u)=msf.read u := by
    change msf.read ((rowPost hv v ((links hv).foldl (linkStep hu hv u v
      (rowPrefix (hu,hv) (u,v)).1) (rowPrefix (hu,hv) (u,v)).2)).1.apply u)=_
    rw [P]
    exact F
  have E := congrArg (fun z : BitVec 1=>z.getLsbD 0) Q
  simpa [msf, Field.read, BitVec.getLsbD_extractLsb', lane] using E

theorem selector_right_pair_no_guard (hu hv : Bool) (u v : BitVec 96)
    (G : ¬selectorGuard hu u v) :
    ((MISByteRows.row (hu,hv) (u,v)).2.apply v).getLsbD 92=v.getLsbD 92 := by
  rw [←localRow_eq]
  have H (w : Fin 3→Bool) (p : Pair (Patch 96)) (L : List Link) :
      msf.read ((L.foldl (linkStep hu hv u v w) p).2.apply v)=msf.read (p.2.apply v) := by
    induction L generalizing p with
    | nil => rfl
    | cons l t IH => exact (IH _).trans (msf_link_right hu hv u v w p l G)
  have Q : msf.read ((localRow (hu,hv) (u,v)).2.apply v)=msf.read v := by
    change msf.read ((rowPost hv v _).2.apply v)=_
    rw [msf_post_right]
    exact (H _ _ _).trans (msf_prefix_right hu hv u v v)
  have E := congrArg (fun z : BitVec 1=>z.getLsbD 0) Q
  simpa [msf, Field.read, BitVec.getLsbD_extractLsb', lane] using E

#print axioms selector_left_pair
#print axioms selector_right_pair_no_guard
set_option maxHeartbeats 4000000

private theorem selector_other_link (hu hv : Bool) (u v : BitVec 96)
    (w : Fin 3→Bool) (p : Pair (Patch 96)) (l : Link) (N : l.src≠0) :
    msf.read ((linkStep hu hv u v w p l).2.apply v)=msf.read (p.2.apply v) := by
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      msf.read ((putK j t).apply x)=msf.read x := ctl_k (by decide) j t x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · rename_i R
    have H : ControllerFrame msf (effect u v hu hv l.src l.dst (w l.src) (oldK hu u l.src)).2.1 := by
      apply msf_effect_right
      · intro _ _ _ _ j0
        exact False.elim (N j0)
      · exact msf_ready_tag _ _ _ _ R
    have E (x : BitVec 96) := H x
    split <;> simp only [Patch.compose_apply,K,E]
  · split
    · rfl
    · split
      · split <;> rfl
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> rfl

theorem selector_right_pair_publish (hu : Bool) (u v : BitVec 96)
    (G : selectorGuard hu u v) :
    ((MISByteRows.row (hu,true) (u,v)).2.apply v).getLsbD 92=
      (((oldK hu u 0).payload/2)%2==1) := by
  rcases G with ⟨tag,hf,op,ha,gw,sel,hs,banked⟩
  let t := oldK hu u 0
  let ix := (t.payload/2)%2
  let pp := rowPrefix (hu,true) (u,v)
  have sel' : selector v=t.payload/4 := sel
  have gw' : grant v 1=true := gw
  have banked' : bank v ix=bitAt t.payload 0 := banked
  have E : (effect u v hu true 0 (some 1) (pp.1 0) t).2.1 =
      (put 92 1 (by decide) ix).compose (putSeal Option.none) := by
    unfold effect ix
    simp [show t.fault=false from hf,show t.opcode=6 from op,
      show t.applied=false from ha,gw',sel',show readSeal v=some t.payload from hs,
      show bank v ((t.payload/2)%2)=bitAt t.payload 0 from banked']
  have R : ready hu u 0 t=true := by
    simp [ready, parked,show t.tag=2 from tag,show t.opcode=6 from op]
  let l0 : Link := ⟨0,some 1⟩
  let l1 : Link := ⟨1,some 2⟩
  let l2 : Link := ⟨2,none⟩
  let step := linkStep hu true u v pp.1
  have K : msf.read ((step pp.2 l0).2.apply v)=BitVec.ofNat 1 ix := by
    rcases P : pp.2 with ⟨a,b⟩
    unfold step l0 linkStep
    dsimp only
    rw [show ready hu u 0 (oldK hu u 0)=true from R,if_pos rfl,Patch.compose_apply,Patch.compose_apply]
    change msf.read ((putK 1 _).apply
      ((effect u v hu true 0 (some 1) (pp.1 0) t).2.1.apply (b.apply v)))=_
    rw [ctl_k (f:=msf) (by decide),E,Patch.compose_apply,msf_seal]
    change msf.read ((msf.assign _).apply _)=_
    rw [Field.read_assign]
  have Q : msf.read ((localRow (hu,true) (u,v)).2.apply v)=BitVec.ofNat 1 ix := by
    change msf.read ((rowPost true v (step (step (step pp.2 l0) l1) l2)).2.apply v)=_
    rw [msf_post_right, selector_other_link _ _ _ _ _ _ _ (by decide),
      selector_other_link _ _ _ _ _ _ _ (by decide)]
    exact K
  rw [←localRow_eq]
  have H := congrArg (fun z : BitVec 1=>z.getLsbD 0) Q
  have IX : ix<2 := Nat.mod_lt _ (by decide)
  have F : (BitVec.ofNat 1 ix).getLsbD 0 = (ix==1) := by
    have I : ix=0 ∨ ix=1 := by omega
    rcases I with J|J <;> rw [J] <;> decide
  rw [F] at H
  simpa only [msf, Field.read, BitVec.getLsbD_extractLsb', lane, Nat.add_zero,
    show (0:Nat)<1 by decide, decide_true, Bool.true_and] using H

#print axioms selector_right_pair_publish

set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

private theorem bankproj_effect_right (u v : BitVec 96) (hu hv : Bool) (j : Fin 3)
    (k : Option (Fin 3)) (w : Bool) (t : Token) :
    ControllerFrame (lane 87 2 (by decide)) (effect u v hu hv j k w t).2.1 := by
  unfold effect
  dsimp only
  split
  · exact ctl_empty _
  split
  · split
    · exact ctl_compose (ctl_put 92 1 (by decide) _ (.inl (by decide)))
        (ctl_put 83 4 (by decide) _ (.inr (by decide)))
    · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · split
    · exact ctl_empty _
    · split <;> exact ctl_empty _
  · exact ctl_empty _

private theorem bankproj_effect_left (u v : BitVec 96) (hu hv : Bool) (l : Link) (w : Bool)
    (tag : (oldK hu u l.src).tag=2) :
    ControllerFrame (lane (88-selector u) 1 (by omega))
      (effect u v hu hv l.src l.dst w (oldK hu u l.src)).1 := by
  let t := oldK hu u l.src
  change ControllerFrame (lane (88-selector u) 1 (by omega)) (effect u v hu hv l.src l.dst w t).1
  have S : selector u<2 := ((lane 92 1 (by decide)).read u).isLt
  unfold effect
  dsimp only
  split
  · exact ctl_empty _
  rename_i F
  have fault : t.fault=false := Bool.eq_false_iff.mpr F
  split
  · split <;> exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact ctl_put 83 4 (by decide) _ (.inr (by change 87≤88-selector u; omega))
  split
  · exact ctl_empty _
  split
  · split
    · exact ctl_empty _
    · rename_i A
      split
      · rename_i B
        have O : 4≤t.opcode := by have := beq_iff_eq.mp B; omega
        have M : selector u=t.payload/4 := by
          have h : (selector u==t.payload/4)=true := by
            by_cases T : (selector u==t.payload/4)=true
            · exact T
            · simp [Bool.eq_false_iff.mpr T] at A
          exact beq_iff_eq.mp h
        have V := (ShortSelectorParity.decoded_descriptor (atGate hu u l.src) ((kField l.src).read u) tag O fault)
        change t.payload<8 ∧ descValid t.payload=true at V
        have D : t.payload/4 ≠ (t.payload/2)%2 := by
          have D := V.2
          simp [descValid] at D
          omega
        have J : (t.payload/2)%2<2 := Nat.mod_lt _ (by decide)
        unfold putBank
        apply ctl_put
        change (88-selector u)+1≤88-(t.payload/2)%2 ∨ (88-(t.payload/2)%2)+1≤88-selector u
        omega
      · exact ctl_put 83 4 (by decide) _ (.inr (by change 87≤88-selector u; omega))
  · exact ctl_empty _

private theorem bankproj_right_step (hu hv : Bool) (u v : BitVec 96) (win : Fin 3→Bool)
    (p : Pair (Patch 96)) (l : Link) :
    let f := lane 87 2 (by decide)
    f.read ((linkStep hu hv u v win p l).2.apply v) = f.read (p.2.apply v) := by
  dsimp only
  let f := lane 87 2 (by decide)
  have F (x) := bankproj_effect_right u v hu hv l.src l.dst (win l.src) (oldK hu u l.src) x
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      (lane 87 2 (by decide)).read ((putK j t).apply x)=(lane 87 2 (by decide)).read x := ctl_k (by decide) j t x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · split <;> simp only [Patch.compose_apply] <;> first | (rw [K]; try rw [F]) | rw [F]
  · split
    · rfl
    · split
      · split <;> rfl
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> rfl

private theorem bankproj_left_step (hv : Bool) (u v : BitVec 96) (win : Fin 3→Bool)
    (p : Pair (Patch 96)) (l : Link) :
    let f := lane (88-selector u) 1 (by omega)
    f.read ((linkStep true hv u v win p l).1.apply u) = f.read (p.1.apply u) := by
  dsimp only
  let f := lane (88-selector u) 1 (by omega)
  have S : selector u<2 := ((lane 92 1 (by decide)).read u).isLt
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      (lane (88-selector u) 1 (by omega)).read ((putK j t).apply x)=(lane (88-selector u) 1 (by omega)).read x := ctl_k (by change 57≤88-selector u; omega) j t x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · rename_i R
    have tag : (oldK true u l.src).tag=2 := by
      unfold ready at R
      exact beq_iff_eq.mp ((Bool.and_eq_true_iff.mp R).1)
    have F (x) := bankproj_effect_left u v true hv l (win l.src) tag x
    split <;> simp only [Patch.compose_apply] <;> first | (rw [K]; try rw [F]) | rw [F]
  · split
    · rfl
    · split
      · split <;> first | rfl | simp only [Patch.compose_apply,K]
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> first | rfl | simp only [Patch.compose_apply,K]

private theorem bankproj_read_fold (f : Field 96 1) (u : BitVec 96)
    (step : Pair (Patch 96)→Link→Pair (Patch 96)) (p : Pair (Patch 96)) (L : List Link)
    (H : ∀ p l, f.read ((step p l).1.apply u)=f.read (p.1.apply u)) :
    f.read ((L.foldl step p).1.apply u)=f.read (p.1.apply u) := by
  induction L generalizing p with
  | nil => rfl
  | cons l L ih => exact (ih _).trans (H _ _)

private theorem bankproj_read_fold_right (f : Field 96 2) (u : BitVec 96)
    (step : Pair (Patch 96)→Link→Pair (Patch 96)) (p : Pair (Patch 96)) (L : List Link)
    (H : ∀ p l, f.read ((step p l).2.apply u)=f.read (p.2.apply u)) :
    f.read ((L.foldl step p).2.apply u)=f.read (p.2.apply u) := by
  induction L generalizing p with
  | nil => rfl
  | cons l L ih => exact (ih _).trans (H _ _)

private theorem bankproj_frame_source (v : BitVec 96) (t : Token) :
    ControllerFrame (lane 87 2 (by decide)) (source v t).1 := by
  unfold source
  dsimp only
  split
  · exact ctl_put 57 26 (by decide) _ (.inr (by decide))
  split
  · refine ctl_compose ?_ (ctl_put 81 2 (by decide) _ (.inr (by decide)))
    split
    · exact ctl_put 57 26 (by decide) _ (.inr (by decide))
    · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact ctl_put 57 26 (by decide) _ (.inr (by decide))
  split
  · exact ctl_put 78 5 (by decide) _ (.inr (by decide))
  · exact ctl_put 78 5 (by decide) _ (.inr (by decide))
  · split
    · exact ctl_put 78 5 (by decide) _ (.inr (by decide))
    · exact ctl_put 57 26 (by decide) _ (.inr (by decide))
  · exact ctl_compose (ctl_compose (ctl_put 78 5 (by decide) _ (.inr (by decide)))
      (ctl_put 72 6 (by decide) _ (.inr (by decide)))) (ctl_put 68 4 (by decide) _ (.inr (by decide)))
  · exact ctl_put 78 5 (by decide) _ (.inr (by decide))
  · exact ctl_put 78 5 (by decide) _ (.inr (by decide))
  · exact ctl_put 57 26 (by decide) _ (.inr (by decide))

/-- Both old receiver banks survive even a successful COMMIT. -/
theorem bankproj_receiver_pair (hu : Bool) (u v : BitVec 96) :
    let f := lane 87 2 (by decide)
    f.read ((MISByteRows.row (hu,true) (u,v)).2.apply v)=f.read v := by
  rw [←localRow_eq]
  dsimp only [localRow]
  let f := lane 87 2 (by decide)
  let pre := rowPrefix (hu,true) (u,v)
  have pref : ControllerFrame f pre.2.2 := by
    have P (b : Bool) : ControllerFrame f
        (if b then grantsPatch (canonical v) else Patch.empty 96) := by
      cases b
      · exact ctl_empty _
      · exact ctl_put 89 3 (by decide) _ (.inl (by decide))
    unfold pre rowPrefix
    dsimp only
    simp only [if_true]
    exact ctl_compose (ctl_compose (ctl_compose (P _)
      (ctl_norm f (by decide) 0 _ _ _)) (ctl_norm f (by decide) 1 _ _ _)) (ctl_norm f (by decide) 2 _ _ _)
  have fold := bankproj_read_fold_right f v (linkStep hu true u v pre.1) pre.2 (links true)
    (bankproj_right_step hu true u v pre.1)
  change f.read ((rowPost true v ((links true).foldl (linkStep hu true u v pre.1) pre.2)).2.apply v)=_
  unfold rowPost
  simp only [if_true,Patch.compose_apply]
  split
  · rw [ctl_empty f]
    exact (bankproj_frame_source v _ _).trans (fold.trans (pref v))
  · rw [ctl_k (f:=f) (by decide)]
    exact (bankproj_frame_source v _ _).trans (fold.trans (pref v))

/-- Outgoing STAGE may write an inactive bank only; the native old selected
bank bit is framed by the actual immutable-old row. -/
theorem bankproj_initiator_pair (hv : Bool) (u v : BitVec 96) :
    let f := lane (88-get u 92 1 (by decide)) 1 (by omega)
    f.read ((MISByteRows.row (true,hv) (u,v)).1.apply u)=f.read u := by
  rw [←localRow_eq]
  dsimp only [localRow]
  let f := lane (88-selector u) 1 (by omega)
  let pre := rowPrefix (true,hv) (u,v)
  have S : selector u<2 := ((lane 92 1 (by decide)).read u).isLt
  have low : 57≤f.offset := by change 57≤88-selector u; omega
  have pref : ControllerFrame f pre.2.1 := by
    unfold pre rowPrefix
    dsimp only
    simp only [if_true]
    exact ctl_compose (ctl_compose (ctl_compose (ctl_put (f:=f) 89 3 (by decide) _
      (.inl (by change 88-selector u+1≤89; omega)))
      (ctl_norm f low 0 _ _ _)) (ctl_norm f low 1 _ _ _)) (ctl_norm f low 2 _ _ _)
  have fold := bankproj_read_fold f u (linkStep true hv u v pre.1) pre.2 (links hv)
    (bankproj_left_step hv u v pre.1)
  change f.read ((rowPost hv v ((links hv).foldl (linkStep true hv u v pre.1) pre.2)).1.apply u)=_
  rw [rowPost_left]
  exact fold.trans (pref u)

#print axioms bankproj_receiver_pair
#print axioms bankproj_initiator_pair

/-- Exact old physical header READ action, using the unpatched old-pair
grant allocator. The two payload banks are kept distinct. -/
def readCapture (u : BitVec 96) (j : Fin 3) (p : Nat) : Nat :=
  setPLane (setPLane p (5-j.val) (selector u==1)) (2-j.val) (bank u (selector u))

private theorem read_effect_packet (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (k : Option (Fin 3)) (win : Bool) (t : Token)
    (op : t.opcode=3) (live : t.fault=false) :
    (effect u v hu hv j k win t).2.2 =
      {t with payload := if hu then
        if win then readCapture u j t.payload else setPLane t.payload 6 false
        else t.payload} := by
  cases t <;> cases hu <;> cases win <;> simp_all [effect,parked,readCapture]

def readWins (hu hv : Bool) (u v : BitVec 96) (j : Fin 3) : Bool :=
  (rowPrefix (hu,hv) (u,v)).1 j

/-- Literal READ transport uses the full unpatched allocator's win bit;
both metadata and a nonheader payload are unchanged by a hop. -/
theorem read_forwardPacket (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (op : (oldK hu u j).opcode=3) (live : (oldK hu u j).fault=false) :
    let t := oldK hu u j
    let w := readWins hu hv u v j
    forwardPacket hu hv u v j k =
      {t with payload := if hu then
        if w then readCapture u j t.payload else setPLane t.payload 6 false
        else t.payload} := by
  unfold forwardPacket
  dsimp only
  rw [read_effect_packet hu hv u v j _ _ _ op live]
  simp [arrival,op,readWins] <;> rfl

/-- Successful READ strips the sticky bit at terminal; a loss emits the
explicit opcode-3 denial rather than a partly captured success. -/
theorem read_turnPacket (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (op : (oldK hu u j).opcode=3) (live : (oldK hu u j).fault=false) :
    let t := oldK hu u j
    let w := readWins hu hv u v j
    let p := if hu then
      if w then readCapture u j t.payload else setPLane t.payload 6 false
      else t.payload
    turnPacket hu hv u v j =
      if bitAt p 6 then {tag:=3, opcode:=3, payload:=p%64}
        else {tag:=3, opcode:=3, outcome:=1} := by
  unfold turnPacket
  dsimp only
  rw [read_effect_packet hu hv u v j _ _ _ op live]
  simp [terminal,op,live,readWins] <;> rfl

private theorem capture_finite :
    ∀ (p : Fin 128) (j : Fin 3) (s b : Bool),
      let q := setPLane (setPLane p.val (5-j.val) s) (2-j.val) b
      q < 128 ∧ bitAt q 6=bitAt p.val 6 ∧ bitAt q (5-j.val)=s ∧
      bitAt q (2-j.val)=b ∧
      ∀ i : Fin 6, i.val≠5-j.val → i.val≠2-j.val → bitAt q i.val=bitAt p.val i.val := by decide

private theorem loss_finite :
    ∀ (p : Fin 128), let q:=setPLane p.val 6 false
    q=p.val%64 ∧ bitAt q 6=false ∧ ∀ i : Fin 6, bitAt q i.val=bitAt p.val i.val := by decide

#print axioms read_forwardPacket
#print axioms read_turnPacket
#print axioms capture_finite
#print axioms loss_finite

/-- Each winning capture records the two assigned low payload bits.
The sticky flag and the other four low bits retain their old values. -/
theorem readCapture_bits (u : BitVec 96) (j : Fin 3) (p : Nat) (P : p<128) :
    let q := readCapture u j p
    q<128 ∧ bitAt q 6=bitAt p 6 ∧
    bitAt q (5-j.val)=(selector u==1) ∧
    bitAt q (2-j.val)=bank u (selector u) ∧
    ∀ i : Fin 6, i.val≠5-j.val → i.val≠2-j.val → bitAt q i.val=bitAt p i.val :=
  capture_finite ⟨p,P⟩ j (selector u==1) (bank u (selector u))

/-- A lost READ changes only the sticky success flag. -/
theorem readLoss_bits (p : Nat) (P : p<128) :
    let q := setPLane p 6 false
    q=p%64 ∧ bitAt q 6=false ∧
    ∀ i : Fin 6, bitAt q i.val=bitAt p i.val :=
  loss_finite ⟨p,P⟩

theorem read_forwardPacket_sticky (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (op : (oldK hu u j).opcode=3) (live : (oldK hu u j).fault=false)
    (P : (oldK hu u j).payload<128) :
    bitAt (forwardPacket hu hv u v j k).payload 6 =
      (bitAt (oldK hu u j).payload 6 && (!hu || readWins hu hv u v j)) := by
  rw [read_forwardPacket _ _ _ _ _ _ op live]
  cases hu
  · simp
  · cases W : readWins true hv u v j
    · simpa [W] using (readLoss_bits _ P).2.1
    · simpa [W] using (readCapture_bits u j _ P).2.1

#print axioms readCapture_bits
#print axioms readLoss_bits
#print axioms read_forwardPacket_sticky

theorem read_forwardPayload_lt (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (op : (oldK hu u j).opcode=3) (live : (oldK hu u j).fault=false)
    (P : (oldK hu u j).payload<128) :
    (forwardPacket hu hv u v j k).payload<128 := by
  rw [read_forwardPacket _ _ _ _ _ _ op live]
  cases hu
  · exact P
  · cases W : readWins true hv u v j
    · have L := (readLoss_bits _ P).1
      simp only [if_true,Bool.false_eq_true,if_false]
      rw [L]
      exact Nat.lt_trans (Nat.mod_lt _ (by decide : 0<64)) (by decide)
    · simpa [W] using (readCapture_bits u j _ P).1

theorem read_is_ready (h : Bool) (x : BitVec 96) (j : Fin 3)
    (F : (oldK h x j).tag=2) (op : (oldK h x j).opcode=3) :
    forwardReady h x j=true := by
  simp [forwardReady,ready,parked,F,op]

#print axioms read_forwardPayload_lt
#print axioms read_is_ready

/-- The terminal's explicit success is equivalent to the old sticky
flag surviving its own header allocation. -/
theorem read_turnPacket_success_iff (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (op : (oldK hu u j).opcode=3) (live : (oldK hu u j).fault=false)
    (P : (oldK hu u j).payload<128) :
    (turnPacket hu hv u v j).outcome=0 ↔
      (bitAt (oldK hu u j).payload 6 && (!hu || readWins hu hv u v j))=true := by
  have H := read_forwardPacket_sticky hu hv u v j 0 op live P
  rw [read_forwardPacket _ _ _ _ _ _ op live] at H
  rw [read_turnPacket _ _ _ _ _ op live]
  dsimp only at H ⊢
  rw [H]
  cases B : bitAt (oldK hu u j).payload 6 && (!hu || readWins hu hv u v j) <;> simp

#print axioms read_turnPacket_success_iff

/-- The payload records a winning capture exactly when the old grant
view on this same outgoing mark wins that lane. -/
theorem readWins_header (hv : Bool) (u v : BitVec 96) (j : Fin 3) :
    readWins true hv u v j = (headerGrantView u).win j := by
  have shape (k : Fin 3) : canonical u k=(headerGrantView u).canonical k := rfl
  have A (k : Fin 3) : (headerGrantView u).ask k =
      ((oldK true u k).tag==2 && !(oldK true u k).fault && (oldK true u k).opcode==3) := rfl
  have R (k : Fin 3) : (headerGrantView u).release k =
      ((oldK true u k).tag==2 && !(oldK true u k).fault && (oldK true u k).opcode==0) := rfl
  unfold readWins rowPrefix
  dsimp only
  simp only [Bool.true_and,dep_eq u _ 0 (by decide),dep_eq u _ 3 (by decide),shape,
    BStarShort.GrantView.win,BStarShort.GrantView.centerWin,A,R]
  by_cases K : j=1 <;> simp [K,Bool.and_left_comm,Bool.and_assoc,Bool.and_comm]

/-- The selected Boolean captured by the literal READ row is the
pre-mark native bank indexed by the old raw selector. -/
theorem readCapture_native (u : BitVec 96) (j : Fin 3) (p : Nat) (P : p<128) :
    bitAt (readCapture u j p) (5-j.val)=u.getLsbD 92 ∧
    bitAt (readCapture u j p) (2-j.val)=u.getLsbD (88-MISByteCodec.get u 92 1 (by decide)) := by
  have C := readCapture_bits u j p P
  have E : (selector u==1)=u.getLsbD 92 := by
    unfold selector MISByteCodec.get
    change (((u.extractLsb' 92 1).toNat)==1)=u.getLsbD 92
    have B : (u.extractLsb' 92 1).toNat<2 := (u.extractLsb' 92 1).isLt
    have D : (u.extractLsb' 92 1).getLsbD 0=u.getLsbD 92 := by
      simp
    rw [←D]
    change (((u.extractLsb' 92 1).toNat)==1)=(u.extractLsb' 92 1).toNat.testBit 0
    have L : (u.extractLsb' 92 1).toNat=0 ∨ (u.extractLsb' 92 1).toNat=1 := by omega
    rcases L with L|L <;> rw [L] <;> decide
  exact ⟨C.2.2.1.trans E,C.2.2.2.1⟩

#print axioms readWins_header
#print axioms readCapture_native
end L4.ShortResetRow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec

open L4.MISByteRows (Link)
open ShortResetFlow
def helloForward : Token := {tag:=2,opcode:=1}
def helloReply : Token := {tag:=3,opcode:=1}

theorem hello_ready (hu : Bool) (u : BitVec 96) (j : Fin 3)
    (H : oldK hu u j=helloForward) : forwardReady hu u j=true := by
  unfold forwardReady
  rw [H]
  rfl

theorem hello_forwardPacket (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (H : oldK hu u j=helloForward) :
    forwardPacket hu hv u v j k=helloForward := by
  unfold forwardPacket
  dsimp only
  rw [H]
  simp [effect,parked,arrival,helloForward]

theorem hello_turnPacket (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (H : oldK hu u j=helloForward) :
    turnPacket hu hv u v j=helloReply := by
  unfold turnPacket
  dsimp only
  rw [H]
  simp [effect,parked,terminal,helloForward,helloReply]

theorem hello_no_ask (u : BitVec 96) (j : Fin 3)
    (H : oldK true u j=helloForward) : (headerGrantView u).ask j=false := by
  change ((oldK true u j).tag==2 && !(oldK true u j).fault &&
    (oldK true u j).opcode==3)=false
  rw [H]
  rfl

#print axioms hello_ready
#print axioms hello_forwardPacket
#print axioms hello_turnPacket
#print axioms hello_no_ask
theorem hello_link_trail_guard (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (a b : Patch 96) (j k : Fin 3) (trail : oldK hu u j=T)
    (r : oldK hv v k=helloForward ∨ oldK hv v k=T) :
    linkStep hu hv u v win (a,b) ⟨j,some k⟩ = (a,b) := by
  rcases r with R | R <;> simp [linkStep,R,trail,ready,T,helloForward]

private theorem hello_prefix_right_frame (hu hv : Bool) (u v : BitVec 96) (k : Fin 3)
    (safe : oldK hv v k=helloForward ∨ oldK hv v k=T) :
    Frames k (rowPrefix (hu,hv) (u,v)).2.2 := by
  let norm := fun j : Fin 3 =>
    let t := oldK hv v j
    if t.fault then putK j t
    else if parked t hv v j && (t.race==1 || t.race==3) then putK j (raceNext t 2)
    else .empty _
  have singles (j : Fin 3) : Frames k (norm j) := by
    by_cases eq : k=j
    · subst j
      rcases safe with S | S
      · simpa [norm,S,helloForward,parked] using empty_frames k
      · simpa [norm,S,T,parked] using empty_frames k
    · dsimp [norm]
      split
      · exact fun x => read_putK_other _ _ eq _ x
      · split
        · exact fun x => read_putK_other _ _ eq _ x
        · exact empty_frames k
  let clear := (resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)
  let base := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else clear
  have base_frame : Frames k base := by
    dsimp [base]
    split
    · split
      · exact keep_high (by decide) _ _
      · exact empty_frames k
    · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
  change Frames k (((base.compose (norm 0)).compose (norm 1)).compose (norm 2))
  exact compose_frames (compose_frames (compose_frames base_frame (singles 0))
    (singles 1)) (singles 2)

/-- An intact trail prevents the incoming selected edge from changing the
next RESET forward or trail slot. Only the freshly installed source K0
can be subject to the independent responder-door action. -/
theorem hello_inbound_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : oldK hv v k=helloForward ∨ oldK hv v k=T) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=(kField k).read v := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k dst)
  have pre_frame (l : Link) (i : l∈pre) : some k≠l.dst := by
    have pw := links_distinct_dst hv
    rw [L] at pw
    have K := (List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp)
    rw [dst] at K
    exact Ne.symm K
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [H,dst,hello_link_trail_guard _ _ _ _ _ _ _ _ _ trail safe,
    fold_right_frame _ _ _ _ _ _ _ _ _ (Z k dst),←H,
    fold_right_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact hello_prefix_right_frame hu hv u v k safe v

theorem hello_root_inbound_frame_pair (hu : Bool) (u v : BitVec 96)
    (wait : get v 81 2 (by decide)=2)
    (op : get v 78 3 (by decide)=1)
    (safe : oldK true v 0=helloForward ∨ oldK true v 0=T) :
    let q := MISByteRows.row (hu,true) (u,v)
    (kField 0).read (q.2.apply v)=(kField 0).read v := by
  have tags : (oldK true v 0).tag=1 ∨ (oldK true v 0).tag=2 := by
    rcases safe with S|S
    · exact .inr (by rw [S]; rfl)
    · exact .inl (by rw [S]; rfl)
  have src := source_wait_holds v (oldK true v 0) wait (by omega) tags
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [post_frame _ _ _ _ (.inr (.inr (congrArg Prod.snd src)))]
  have H (l : Link) (M : l∈links true) : some (0 : Fin 3)≠l.dst := by
    change l∈([⟨0,some 1⟩,⟨1,some 2⟩,⟨2,none⟩] : List Link) at M
    simp only [List.mem_cons,List.not_mem_nil,or_false] at M
    rcases M with A|A|A <;> subst l <;> decide
  rw [fold_right_frame _ _ _ _ _ _ _ _ _ H]
  exact hello_prefix_right_frame hu true u v 0 safe v

theorem hello_prefix_trail_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : oldK hv v k=helloForward ∨ oldK hv v k=T) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=(kField j).read u := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame (l : Link) (i : l∈pre) : j≠l.src := by
    have pw := links_distinct_src hv
    rw [L] at pw
    exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp))
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  rw [H,dst,hello_link_trail_guard _ _ _ _ _ _ _ _ _ trail safe,
    fold_left_frame _ _ _ _ _ _ _ _ _ A,←H,
    fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact prefix_left_trail_frame hu hv u v j trail u


#print axioms hello_inbound_frame_pair
#print axioms hello_root_inbound_frame_pair
#print axioms hello_prefix_trail_frame_pair
end L4.ShortResetRow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow
open L4.MISByteRows (Link)

def readFront (data : Nat) : Token := {tag:=2, opcode:=3, payload:=data}

theorem read_link_trail_guard (data : Nat) (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (a b : Patch 96) (j k : Fin 3) (trail : oldK hu u j=T)
    (r : oldK hv v k=readFront data ∨ oldK hv v k=T) :
    linkStep hu hv u v win (a,b) ⟨j,some k⟩ = (a,b) := by
  rcases r with R | R <;> simp [linkStep,R,trail,ready,T,readFront]

private theorem read_prefix_right_frame (data : Nat) (hu hv : Bool) (u v : BitVec 96) (k : Fin 3)
    (safe : oldK hv v k=readFront data ∨ oldK hv v k=T) :
    Frames k (rowPrefix (hu,hv) (u,v)).2.2 := by
  let norm := fun j : Fin 3 =>
    let t := oldK hv v j
    if t.fault then putK j t
    else if parked t hv v j && (t.race==1 || t.race==3) then putK j (raceNext t 2)
    else .empty _
  have singles (j : Fin 3) : Frames k (norm j) := by
    by_cases eq : k=j
    · subst j
      rcases safe with S | S
      · simpa [norm,S,readFront,parked] using empty_frames k
      · simpa [norm,S,T,parked] using empty_frames k
    · dsimp [norm]
      split
      · exact fun x => read_putK_other _ _ eq _ x
      · split
        · exact fun x => read_putK_other _ _ eq _ x
        · exact empty_frames k
  let clear := (resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)
  let base := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else clear
  have base_frame : Frames k base := by
    dsimp [base]
    split
    · split
      · exact keep_high (by decide) _ _
      · exact empty_frames k
    · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
  change Frames k (((base.compose (norm 0)).compose (norm 1)).compose (norm 2))
  exact compose_frames (compose_frames (compose_frames base_frame (singles 0))
    (singles 1)) (singles 2)

/-- An intact trail prevents the incoming selected edge from changing the
next RESET forward or trail slot. Only the freshly installed source K0
can be subject to the independent responder-door action. -/
theorem read_inbound_frame_pair (data : Nat) (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : oldK hv v k=readFront data ∨ oldK hv v k=T) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=(kField k).read v := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k dst)
  have pre_frame (l : Link) (i : l∈pre) : some k≠l.dst := by
    have pw := links_distinct_dst hv
    rw [L] at pw
    have K := (List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp)
    rw [dst] at K
    exact Ne.symm K
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [H,dst,read_link_trail_guard data _ _ _ _ _ _ _ _ _ trail safe,
    fold_right_frame _ _ _ _ _ _ _ _ _ (Z k dst),←H,
    fold_right_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact read_prefix_right_frame data hu hv u v k safe v

theorem read_root_inbound_frame_pair (data : Nat) (hu : Bool) (u v : BitVec 96)
    (wait : get v 81 2 (by decide)=2)
    (op : get v 78 3 (by decide)=3)
    (safe : oldK true v 0=readFront data ∨ oldK true v 0=T) :
    let q := MISByteRows.row (hu,true) (u,v)
    (kField 0).read (q.2.apply v)=(kField 0).read v := by
  have tags : (oldK true v 0).tag=1 ∨ (oldK true v 0).tag=2 := by
    rcases safe with S|S
    · exact .inr (by rw [S]; rfl)
    · exact .inl (by rw [S]; rfl)
  have src := source_wait_holds v (oldK true v 0) wait (by omega) tags
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [post_frame _ _ _ _ (.inr (.inr (congrArg Prod.snd src)))]
  have H (l : Link) (M : l∈links true) : some (0 : Fin 3)≠l.dst := by
    change l∈([⟨0,some 1⟩,⟨1,some 2⟩,⟨2,none⟩] : List Link) at M
    simp only [List.mem_cons,List.not_mem_nil,or_false] at M
    rcases M with A|A|A <;> subst l <;> decide
  rw [fold_right_frame _ _ _ _ _ _ _ _ _ H]
  exact read_prefix_right_frame data hu true u v 0 safe v

theorem read_prefix_trail_frame_pair (data : Nat) (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : oldK hv v k=readFront data ∨ oldK hv v k=T) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=(kField j).read u := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame (l : Link) (i : l∈pre) : j≠l.src := by
    have pw := links_distinct_src hv
    rw [L] at pw
    exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp))
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  rw [H,dst,read_link_trail_guard data _ _ _ _ _ _ _ _ _ trail safe,
    fold_left_frame _ _ _ _ _ _ _ _ _ A,←H,
    fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact prefix_left_trail_frame hu hv u v j trail u



#print axioms read_inbound_frame_pair
#print axioms read_root_inbound_frame_pair
#print axioms read_prefix_trail_frame_pair
end L4.ShortResetRow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow
open L4.MISByteRows (Link)
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- The STAGE/SEAL centre guard reads the pre-interaction grant and selector. -/
def stageSealOwner (u : BitVec 96) (payload : Nat) : Bool :=
  u.getLsbD 90 && get u 92 1 (by decide) == payload / 4

/-- SEAL additionally requires the staged bit in the indicated old bank. -/
def sealBankMatches (u : BitVec 96) (payload : Nat) : Bool :=
  u.getLsbD (88 - (payload / 2) % 2) == (payload % 2 == 1)

/-- Exact token emitted by the centre effect on a STAGE packet. -/
theorem stage_effect_center (u v : BitVec 96) (hv win : Bool)
    (k : Option (Fin 3)) (t : Token) (hF : t.fault = false) (hO : t.opcode = 4) :
    effect u v true hv 1 k win t =
      if stageSealOwner u t.payload then
        (put (88 - (t.payload / 2) % 2) 1 (by omega)
          (t.payload % 2 == 1).toNat, Patch.empty 96, t)
      else (Patch.empty 96, Patch.empty 96, faultToken 2) := by
  have O : (grant u 1 && selector u == t.payload / 4) = stageSealOwner u t.payload := rfl
  cases h : stageSealOwner u t.payload <;>
    simp [effect, hF, hO, parked, O, h, putBank, bitAt]

/-- Exact SEAL patch (and no responder patch), or fault with no effect.
The bank check is on the old word, not the result of any simultaneous patch. -/
theorem seal_effect_center (u v : BitVec 96) (hv win : Bool)
    (k : Option (Fin 3)) (t : Token) (hF : t.fault = false) (hO : t.opcode = 5) :
    effect u v true hv 1 k win t =
      if stageSealOwner u t.payload && sealBankMatches u t.payload then
        (put 83 4 (by decide) (8 + t.payload), Patch.empty 96, t)
      else (Patch.empty 96, Patch.empty 96, faultToken 2) := by
  have O : (grant u 1 && selector u == t.payload / 4) = stageSealOwner u t.payload := rfl
  have B : (bank u ((t.payload/2)%2) != bitAt t.payload 0) =
      !(sealBankMatches u t.payload) := rfl
  cases h : stageSealOwner u t.payload <;> cases m : sealBankMatches u t.payload <;>
    simp [effect, hF, hO, parked, O, h, B, m, putSeal]

private theorem stage_seal_forward_ready (u : BitVec 96) (t : Token)
    (ht : oldK true u 1 = t) (htag : t.tag = 2)
    (hop : t.opcode = 4 ∨ t.opcode = 5) :
    forwardReady true u 1 = true := by
  rcases hop with h | h <;> simp [forwardReady, ht, ready, parked, htag, h]

/-- A selected STAGE4 centre crossing writes the exact trail and either the
unchanged packet or a fault at the successor. The centre guard uses old bytes. -/
theorem stage_forward_pair (hv : Bool) (u v : BitVec 96) (k : Fin 3) (t : Token)
    (dst : destination hv 1 = some k)
    (ht : oldK true u 1 = t) (htag : t.tag = 2)
    (hF : t.fault = false) (hop : t.opcode = 4) :
    let q := MISByteRows.row (true,hv) (u,v)
    (kField 1).read (q.1.apply u) = encode T ∧
    (kField k).read (q.2.apply v) =
      encode (if stageSealOwner u t.payload then t else faultToken 2) := by
  have out := forward_ready_out_pair true hv u v 1 k dst
    (stage_seal_forward_ready u t ht htag (.inl hop))
  simp only [forwardPacket, ht, stage_effect_center _ _ _ _ _ _ hF hop] at out
  cases h : stageSealOwner u t.payload <;> simpa [h, arrival, hF, hop, faultToken] using out

/-- The analogous selected SEAL5 crossing also uses the old bank bit. -/
theorem seal_forward_pair (hv : Bool) (u v : BitVec 96) (k : Fin 3) (t : Token)
    (dst : destination hv 1 = some k)
    (ht : oldK true u 1 = t) (htag : t.tag = 2)
    (hF : t.fault = false) (hop : t.opcode = 5) :
    let q := MISByteRows.row (true,hv) (u,v)
    (kField 1).read (q.1.apply u) = encode T ∧
    (kField k).read (q.2.apply v) = encode
      (if stageSealOwner u t.payload && sealBankMatches u t.payload then t else faultToken 2) := by
  have out := forward_ready_out_pair true hv u v 1 k dst
    (stage_seal_forward_ready u t ht htag (.inr hop))
  simp only [forwardPacket, ht, seal_effect_center _ _ _ _ _ _ hF hop] at out
  cases h : (stageSealOwner u t.payload && sealBankMatches u t.payload) <;>
    simpa [h, arrival, hF, hop, faultToken] using out

#print axioms stage_effect_center
#print axioms seal_effect_center
#print axioms stage_forward_pair
#print axioms seal_forward_pair

private theorem effect_left_noncenter {n : Nat} (f : Field 96 n)
    (u v : BitVec 96) (hv : Bool) (l : Link) (w : Bool) (t : Token) (hn : l.src ≠ 1) :
    ControllerFrame f (effect u v true hv l.src l.dst w t).1 := by
  unfold effect
  dsimp only
  have z : (l.src==1)=false := Bool.eq_false_iff.mpr (fun H => hn (beq_iff_eq.mp H))
  simp only [z,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]
  split
  · apply ctl_empty
  split
  · split <;> apply ctl_empty
  split
  · apply ctl_empty
  split <;> apply ctl_empty

private theorem stage_seal_prefix_frame {n : Nat} (f : Field 96 n)
    (lo : 57 ≤ f.offset) (hi : f.offset + n ≤ 89) (hv : Bool) (u v : BitVec 96) :
    ControllerFrame f (rowPrefix (true,hv) (u,v)).2.1 := by
  let norm := fun j : Fin 3 =>
    let t := oldK true u j
    if t.fault then putK j t
    else if parked t true u j && (t.race==1 || t.race==2) then putK j (raceNext t 3)
    else .empty _
  have N (j : Fin 3) : ControllerFrame f (norm j) := by
    unfold norm
    dsimp only
    split
    · exact ctl_k lo _ _
    split
    · exact ctl_k lo _ _
    · exact ctl_empty _
  unfold rowPrefix
  dsimp only [Prod.fst, Prod.snd, if_true]
  exact ctl_compose (ctl_compose (ctl_compose
    (ctl_put 89 3 (by decide) _ (.inl hi)) (N 0)) (N 1)) (N 2)

private theorem stage_seal_left_field {n : Nat} (f : Field 96 n)
    (lo : 57 ≤ f.offset) (hi : f.offset + n ≤ 89)
    (hv : Bool) (u v : BitVec 96) (t : Token) (d : Patch 96)
    (ht : oldK true u 1 = t) (htag : t.tag = 2)
    (hop : t.opcode = 4 ∨ t.opcode = 5)
    (D : ∀ k w x, f.read ((effect u v true hv 1 k w t).1.apply x) =
      f.read (d.apply x))
    (DF : ∀ x, f.read x = f.read u → f.read (d.apply x) = f.read (d.apply u)) :
    f.read ((MISByteRows.row (true,hv) (u,v)).1.apply u) = f.read (d.apply u) := by
  have rdy : ready true u 1 t = true := by
    have F := stage_seal_forward_ready u t ht htag hop
    simpa [forwardReady, ht] using F
  have K (j : Fin 3) (q : Token) (x : BitVec 96) :
      f.read ((putK j q).apply x)=f.read x := ctl_k lo j q x
  have C (w : Fin 3 → Bool) (p : Pair (Patch 96)) (k : Option (Fin 3))
      (P : f.read (p.1.apply u) = f.read u) :
      f.read ((linkStep true hv u v w p ⟨1,k⟩).1.apply u) = f.read (d.apply u) := by
    rcases p with ⟨a,b⟩
    unfold linkStep
    dsimp only
    rw [ht, rdy]
    cases k <;> simp only [if_true, Patch.compose_apply, K, D]
    all_goals exact DF _ P
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [rowPost_left]
  have P := stage_seal_prefix_frame f lo hi hv u v u
  generalize (rowPrefix (true,hv) (u,v)).1 = w
  generalize (rowPrefix (true,hv) (u,v)).2 = p at P ⊢
  cases hv <;> simp only [links,if_true,if_false,Bool.false_eq_true,List.foldl_cons,List.foldl_nil]
  · rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨2,some 2⟩
        (effect_left_noncenter f _ _ _ _ _ _ (by decide))]
    apply C
    rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨0,some 0⟩
        (effect_left_noncenter f _ _ _ _ _ _ (by decide))]
    exact P
  · rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨2,none⟩
        (effect_left_noncenter f _ _ _ _ _ _ (by decide))]
    apply C
    rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨0,some 1⟩
        (effect_left_noncenter f _ _ _ _ _ _ (by decide))]
    exact P

/-- Full initiator bank projection of the old-pair STAGE4 row. Every
bank other than the named bank is unchanged, including on failure. -/
theorem stage_bank_pair (hv : Bool) (u v : BitVec 96) (t : Token) (i : Fin 2)
    (ht : oldK true u 1 = t) (htag : t.tag = 2)
    (hF : t.fault = false) (hop : t.opcode = 4) :
    let f := lane (88-i.val) 1 (by omega)
    let q := MISByteRows.row (true,hv) (u,v)
    f.read (q.1.apply u) =
      if stageSealOwner u t.payload && i.val == (t.payload / 2) % 2 then
        BitVec.ofNat 1 (t.payload % 2 == 1).toNat else f.read u := by
  dsimp only
  let d := if stageSealOwner u t.payload then
    put (88 - (t.payload / 2) % 2) 1 (by omega) (t.payload % 2 == 1).toNat
    else Patch.empty 96
  let f := lane (88-i.val) 1 (by omega)
  have W (x : BitVec 96) : f.read (d.apply x) =
      if stageSealOwner u t.payload && i.val == (t.payload / 2) % 2 then
        BitVec.ofNat 1 (t.payload % 2 == 1).toNat else f.read x := by
    unfold d
    split
    · rename_i own
      by_cases ix : i.val = (t.payload / 2) % 2
      · simp only [own,ix,beq_self_eq_true,Bool.and_self,if_true]
        have F : f = lane (88-(t.payload/2)%2) 1 (by omega) := by
          unfold f lane
          congr 1
          omega
        rw [F]
        exact Field.read_assign _ _ _
      · simp only [own, Bool.true_and, beq_iff_eq, ix, if_false]
        apply ctl_put
        have il := i.isLt
        change 88-i.val+1 ≤ 88-(t.payload/2)%2 ∨
          88-(t.payload/2)%2+1 ≤ 88-i.val
        omega
    · rename_i own
      have h : stageSealOwner u t.payload = false := Bool.eq_false_iff.mpr own
      simpa only [h,Bool.false_and,Bool.false_eq_true,if_false] using ctl_empty f x
  exact (stage_seal_left_field f (by change 57 ≤ 88-i.val; omega)
    (by change 88-i.val+1 ≤ 89; omega) hv u v t d ht htag (.inl hop)
    (by
      intro k w x
      rw [stage_effect_center _ _ _ _ _ _ hF hop]
      unfold d
      split <;> rfl)
    (by
      intro x X
      rw [W, W, X])).trans (W u)

/-- Full initiator seal projection of the old-pair SEAL5 row. The
only write is the low four bits of 8 + payload when both guards hold. -/
theorem seal_value_pair (hv : Bool) (u v : BitVec 96) (t : Token)
    (ht : oldK true u 1 = t) (htag : t.tag = 2)
    (hF : t.fault = false) (hop : t.opcode = 5) :
    let f := lane 83 4 (by decide)
    let q := MISByteRows.row (true,hv) (u,v)
    f.read (q.1.apply u) =
      if stageSealOwner u t.payload && sealBankMatches u t.payload then
        BitVec.ofNat 4 (8 + t.payload) else f.read u := by
  dsimp only
  let d := if stageSealOwner u t.payload && sealBankMatches u t.payload then
    put 83 4 (by decide) (8+t.payload) else Patch.empty 96
  let f := lane 83 4 (by decide)
  have W (x : BitVec 96) : f.read (d.apply x) =
      if stageSealOwner u t.payload && sealBankMatches u t.payload then
        BitVec.ofNat 4 (8 + t.payload) else f.read x := by
    unfold d
    split
    · exact Field.read_assign _ _ _
    · exact ctl_empty f x
  exact (stage_seal_left_field f (by decide) (by decide) hv u v t d ht htag (.inr hop)
    (by
      intro k w x
      rw [seal_effect_center _ _ _ _ _ _ hF hop]
      unfold d
      split <;> rfl)
    (by
      intro x X
      rw [W, W, X])).trans (W u)

#print axioms stage_bank_pair
#print axioms seal_value_pair
end L4.ShortResetRow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow

/-- Old-pair COMMIT6 guard, evaluated on the next centre's old header. -/
def commitAccept (v : BitVec 96) (t : Token) : Bool :=
  !t.applied && grant v 1 && selector v==t.payload/4 &&
    readSeal v==some t.payload && bank v ((t.payload/2)%2)==bitAt t.payload 0

theorem selectorGuard_iff_commitAccept (hu : Bool) (u v : BitVec 96) :
    let t := oldK hu u 0
    selectorGuard hu u v ↔ t.tag=2 ∧ t.fault=false ∧ t.opcode=6 ∧ commitAccept v t=true := by
  dsimp only [selectorGuard,commitAccept,grant,selector,bank,bitAt]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Nat.shiftRight_zero]
  constructor
  · rintro ⟨a,b,c,d,e,f,g,h⟩
    exact ⟨a,b,c,⟨⟨⟨d,e⟩,f⟩,g⟩,h⟩
  · rintro ⟨a,b,c,⟨⟨⟨d,e⟩,f⟩,g⟩,h⟩
    exact ⟨a,b,c,d,e,f,g,h⟩

#print axioms selectorGuard_iff_commitAccept

/-- COMMIT6 centre execution writes the selector and consumes the seal only
when all guard fields agree. A rejected execution has an empty effect patch. -/
theorem commit_centre_effect (hu : Bool) (u v : BitVec 96) (w : Bool) (t : Token)
    (op : t.opcode=6) (live : t.fault=false) :
    effect u v hu true 0 (some 1) w t =
      if commitAccept v t then
        (Patch.empty 96, (put 92 1 (by decide) ((t.payload/2)%2)).compose
          (putSeal Option.none), {t with applied:=true})
      else (Patch.empty 96,Patch.empty 96,faultToken 2) := by
  simp [effect,commitAccept,op,live]

theorem commit_is_ready (hu : Bool) (u : BitVec 96) (j : Fin 3)
    (front : (oldK hu u j).tag=2) (op : (oldK hu u j).opcode=6) :
    forwardReady hu u j=true := by
  simp [forwardReady,ready,parked,front,op]

/-- A centre entrance is the only COMMIT6 row that can update the applied bit. -/
theorem commit_forwardPacket_centre (hu : Bool) (u v : BitVec 96)
    (op : (oldK hu u 0).opcode=6) (live : (oldK hu u 0).fault=false) :
    let t := oldK hu u 0
    forwardPacket hu true u v 0 1 =
      if commitAccept v t then {t with applied:=true} else faultToken 2 := by
  dsimp only
  unfold forwardPacket
  dsimp only
  rw [commit_centre_effect _ _ _ _ _ op live]
  by_cases H : commitAccept v (oldK hu u 0)
  · simp [H,arrival,op]
  · simp [H,arrival,faultToken]

/-- Off the centre entrance, COMMIT6 relays the whole old packet unchanged,
including the applied and fault fields. -/
theorem commit_forwardPacket_relay (hu hv : Bool) (u v : BitVec 96)
    (j k : Fin 3) (op : (oldK hu u j).opcode=6)
    (notCentre : ¬ (hv=true ∧ j=0 ∧ k=1)) :
    forwardPacket hu hv u v j k=oldK hu u j := by
  have no : ¬ ((hv=true ∧ j=0) ∧ k=1) :=
    fun ⟨⟨a,b⟩,c⟩ => notCentre ⟨a,b,c⟩
  have E : (effect u v hu hv j (some k) ((rowPrefix (hu,hv) (u,v)).1 j)
      (oldK hu u j)).2.2=oldK hu u j := by
    cases H : (oldK hu u j).fault <;> simp [effect,op,no,parked,H]
  unfold forwardPacket
  dsimp only
  rw [E]
  simp [arrival,op]

/-- The terminal never applies COMMIT6 itself. It produces a success exactly
for a nonfaulty COMMIT6 carrying its applied bit. -/
theorem commit_turnPacket (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (op : (oldK hu u j).opcode=6) :
    let t := oldK hu u j
    turnPacket hu hv u v j =
      if t.fault || !t.applied then faultToken 3 else {tag:=3,opcode:=6} := by
  simp [turnPacket,effect,parked,terminal,op]

theorem commit_turnPacket_success_iff (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (op : (oldK hu u j).opcode=6) :
    (turnPacket hu hv u v j).fault=false ↔
      (oldK hu u j).fault=false ∧ (oldK hu u j).applied=true := by
  rw [commit_turnPacket _ _ _ _ _ op]
  cases (oldK hu u j).fault <;> cases (oldK hu u j).applied <;>
    simp [faultToken]

theorem commit_centre_out_pair (hu : Bool) (u v : BitVec 96)
    (front : (oldK hu u 0).tag=2)
    (op : (oldK hu u 0).opcode=6) (live : (oldK hu u 0).fault=false) :
    let q := MISByteRows.row (hu,true) (u,v)
    let t := oldK hu u 0
    (kField 0).read (q.1.apply u)=encode T ∧
      (kField 1).read (q.2.apply v)=
        encode (if commitAccept v t then {t with applied:=true} else faultToken 2) := by
  have H := forward_ready_out_pair hu true u v 0 1 rfl (commit_is_ready hu u 0 front op)
  simpa only [commit_forwardPacket_centre hu u v op live] using H

#print axioms commit_is_ready
#print axioms commit_forwardPacket_centre
#print axioms commit_forwardPacket_relay
#print axioms commit_turnPacket
#print axioms commit_turnPacket_success_iff
#print axioms commit_centre_out_pair

theorem commit_relay_out_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k)
    (front : (oldK hu u j).tag=2) (op : (oldK hu u j).opcode=6)
    (notCentre : ¬ (hv=true ∧ j=0 ∧ k=1)) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode T ∧
      (kField k).read (q.2.apply v)=encode (oldK hu u j) := by
  have H := forward_ready_out_pair hu hv u v j k dst (commit_is_ready hu u j front op)
  simpa only [commit_forwardPacket_relay hu hv u v j k op notCentre] using H

theorem commit_terminal_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (dst : destination hv j=none)
    (front : (oldK hu u j).tag=2) (op : (oldK hu u j).opcode=6) :
    let q := MISByteRows.row (hu,hv) (u,v)
    let t := oldK hu u j
    (kField j).read (q.1.apply u) =
      encode (if t.fault || !t.applied then faultToken 3 else {tag:=3,opcode:=6}) := by
  have H := forward_ready_turn_pair hu hv u v j dst (commit_is_ready hu u j front op)
  simpa only [commit_turnPacket hu hv u v j op] using H

#print axioms commit_centre_effect
#print axioms commit_relay_out_pair
#print axioms commit_terminal_pair

end L4.ShortResetRow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow

private theorem admit_live_ungated_ready (hu : Bool) (u : BitVec 96) (j : Fin 3)
    (t : Token) (old : oldK hu u j = t)
    (tag : t.tag = 2) (gate : atGate hu u j = false) : forwardReady hu u j = true := by
  simp [forwardReady, old, ready, parked, gate, tag]

/-- Once ADMIT leaves the selected centre it transports the chosen payload.
An ordinary ungated hop does not recompute admission; entry into a gate
initializes only the race to 1. -/
theorem admit_ungated_out_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3) (t : Token)
    (dst : destination hv j = some k) (old : oldK hu u j = t)
    (tag : t.tag = 2) (op : t.opcode = 2) (live : t.fault = false)
    (gate : atGate hu u j = false) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u) = encode T ∧
      (kField k).read (q.2.apply v) =
        encode (if atGate hv v k then {t with race := 1} else t) := by
  have H := forward_ready_out_pair hu hv u v j k dst
    (admit_live_ungated_ready hu u j t old tag gate)
  simpa [forwardPacket, old, effect, op, live, parked, gate, arrival] using H

/-- Terminal short ADMIT2 copies the already-chosen payload to the D2 reply.
Payload 1 and payload 0 are both ordinary, nonfaulting returns. -/
theorem admit_ungated_turn_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3) (t : Token)
    (dst : destination hv j = none) (old : oldK hu u j = t)
    (tag : t.tag = 2) (op : t.opcode = 2) (live : t.fault = false)
    (gate : atGate hu u j = false) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u) = encode {tag := 3, opcode := 2, payload := t.payload} := by
  have H := forward_ready_turn_pair hu hv u v j dst
    (admit_live_ungated_ready hu u j t old tag gate)
  simpa [turnPacket, old, effect, op, live, parked, gate, terminal] using H

/-- The literal terminal lane is always ungated. This uses the destination
table alone and does not assume a legitimate layout or header word. -/
theorem admit_terminal_ungated (hu hv : Bool) (u : BitVec 96) (j : Fin 3)
    (dst : destination hv j = none) : atGate hu u j = false := by
  have ne : j ≠ (1 : Fin 3) := by
    intro H
    subst j
    cases hv <;> contradiction
  have hvj : j.val ≠ 1 := fun h => ne (Fin.ext h)
  simp [atGate, hvj]

#print axioms admit_ungated_out_pair
#print axioms admit_ungated_turn_pair
#print axioms admit_terminal_ungated
end L4.ShortResetRow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow
set_option linter.unusedSimpArgs false

private theorem stage_seal_noncenter_effect (u v : BitVec 96) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Token)
    (liveOp : t.opcode = 4 ∨ t.opcode = 5) (nc : hu = false ∨ j ≠ 1) :
    effect u v hu hv j k win t = (Patch.empty 96, Patch.empty 96, t) := by
  have N : (hu && j == 1) = false := by
    rcases nc with hh | hj
    · simp [hh]
    · simp [hj]
  rcases liveOp with op | op <;> cases hf : t.fault <;>
    simp [effect, parked, op, N, hf]

private theorem write_ack_forward_ready (hu : Bool) (u : BitVec 96) (j : Fin 3)
    (t : Token) (old : oldK hu u j = t) (tag : t.tag = 2)
    (kind : t.opcode = 4 ∨ t.opcode = 5 ∨ t.fault = true) :
    forwardReady hu u j = true := by
  rcases kind with n | n | n <;> simp [forwardReady, old, ready, parked, tag, n]

/-- At a non-centre occurrence, a live STAGE4 or SEAL5 forwards the
entire descriptor unchanged. An already-faulty forward is sticky at
any occurrence, including at the centre. -/
theorem write_ack_forward_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (t : Token) (dst : destination hv j = some k) (old : oldK hu u j = t)
    (tag : t.tag = 2)
    (kind : ((t.opcode = 4 ∨ t.opcode = 5) ∧ (hu = false ∨ j ≠ 1)) ∨ t.fault = true) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u) = encode T ∧ (kField k).read (q.2.apply v) = encode t := by
  have K : t.opcode = 4 ∨ t.opcode = 5 ∨ t.fault = true := by
    rcases kind with ⟨h|h,_⟩ | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  have H := forward_ready_out_pair hu hv u v j k dst
    (write_ack_forward_ready hu u j t old tag K)
  rcases kind with ⟨op,nc⟩ | bad
  · simp only [forwardPacket, old, stage_seal_noncenter_effect _ _ _ _ _ _ _ _ op nc] at H
    rcases op with op | op <;> simpa [arrival, op] using H
  · simpa [forwardPacket, old, effect, bad, arrival] using H

/-- Native terminal D4/D5 returns have zero payload; a faulty F instead
turns into the canonical fault D with no positive acknowledgement. -/
theorem write_ack_turn_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (t : Token) (dst : destination hv j = none) (old : oldK hu u j = t)
    (tag : t.tag = 2)
    (kind : t.opcode = 4 ∨ t.opcode = 5 ∨ t.fault = true) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u) =
      encode (if t.fault then faultToken 3 else {tag := 3, opcode := t.opcode}) := by
  have H := forward_ready_turn_pair hu hv u v j dst
    (write_ack_forward_ready hu u j t old tag kind)
  have N : j ≠ (1 : Fin 3) := by
    intro hh
    subst j
    cases hv <;> contradiction
  rcases kind with op | op | bad
  · simpa [turnPacket, old, stage_seal_noncenter_effect _ _ _ _ _ _ _ _ (.inl op) (.inr N),
      terminal, op] using H
  · simpa [turnPacket, old, stage_seal_noncenter_effect _ _ _ _ _ _ _ _ (.inr op) (.inr N),
      terminal, op] using H
  · simpa [turnPacket, old, effect, terminal, bad] using H

#print axioms write_ack_forward_pair
#print axioms write_ack_turn_pair
end L4.ShortResetRow


namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow
open L4.MISByteRows (Link)

/-- A forward token that cannot be parked in the opcode-2 gate race,
or a trail. In particular, canonical faults (even opcode 2) qualify. -/
def InboundToken (t : Token) : Prop :=
  (t.tag=1 ∨ t.tag=2) ∧ (t.fault=true ∨ t.opcode≠2)

private theorem nonparked_link_trail_guard (hu hv : Bool) (u v : BitVec 96)
    (win : Fin 3 → Bool) (a b : Patch 96) (j k : Fin 3)
    (trail : oldK hu u j=T) (safe : InboundToken (oldK hv v k)) :
    linkStep hu hv u v win (a,b) ⟨j,some k⟩ = (a,b) := by
  rcases safe.1 with tag | tag <;>
    simp [linkStep, trail, ready, T, tag]

private theorem nonparked_prefix_right_frame (hu hv : Bool) (u v : BitVec 96)
    (k : Fin 3) (safe : InboundToken (oldK hv v k))
    (wire : (oldK hv v k).fault=true → encode (oldK hv v k)=(kField k).read v) :
    (kField k).read ((rowPrefix (hu,hv) (u,v)).2.2.apply v)=(kField k).read v := by
  let norm := fun j : Fin 3 =>
    let t := oldK hv v j
    if t.fault then putK j t
    else if parked t hv v j && (t.race==1 || t.race==3) then putK j (raceNext t 2)
    else .empty _
  have singles (j : Fin 3) (x : BitVec 96)
      (X : (kField k).read x=(kField k).read v) :
      (kField k).read ((norm j).apply x)=(kField k).read v := by
    by_cases eq : k=j
    · subst j
      cases F : (oldK hv v k).fault
      · have op : (oldK hv v k).opcode≠2 := safe.2.resolve_left (by simp [F])
        have hold : norm k=.empty _ := by simp [norm,F,parked,op]
        rw [hold,empty_frames k x,X]
      · have hold : norm k=putK k (oldK hv v k) := by simp [norm,F]
        rw [hold,putK,Field.read_assign,wire F]
    · have K : Frames k (norm j) := by
        dsimp [norm]
        split
        · exact fun y => read_putK_other _ _ eq _ y
        · split
          · exact fun y => read_putK_other _ _ eq _ y
          · exact empty_frames k
      exact (K x).trans X
  let clear := (resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)
  let base := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else clear
  have base_frame : Frames k base := by
    dsimp [base]
    split
    · split
      · exact keep_high (by decide) _ _
      · exact empty_frames k
    · exact compose_frames (compose_frames (keep_high (by decide) _ _)
        (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
  change (kField k).read ((((base.compose (norm 0)).compose (norm 1)).compose (norm 2)).apply v)=_
  simp only [Patch.compose_apply]
  exact singles 2 _ (singles 1 _ (singles 0 _ (base_frame v)))

theorem nonparked_inbound_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : InboundToken (oldK hv v k))
    (wire : (oldK hv v k).fault=true → encode (oldK hv v k)=(kField k).read v) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=(kField k).read v := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k dst)
  have pre_frame (l : Link) (i : l∈pre) : some k≠l.dst := by
    have pw := links_distinct_dst hv
    rw [L] at pw
    have K := (List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp)
    rw [dst] at K
    exact Ne.symm K
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [H,dst,nonparked_link_trail_guard _ _ _ _ _ _ _ _ _ trail safe,
    fold_right_frame _ _ _ _ _ _ _ _ _ (Z k dst),←H,
    fold_right_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact nonparked_prefix_right_frame hu hv u v k safe wire

theorem nonparked_root_inbound_frame_pair (hu : Bool) (u v : BitVec 96)
    (wait : get v 81 2 (by decide)=2)
    (op : get v 78 3 (by decide) < 7)
    (safe : InboundToken (oldK true v 0))
    (wire : (oldK true v 0).fault=true → encode (oldK true v 0)=(kField 0).read v) :
    let q := MISByteRows.row (hu,true) (u,v)
    (kField 0).read (q.2.apply v)=(kField 0).read v := by
  have src := source_wait_holds v (oldK true v 0) wait op safe.1
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [post_frame _ _ _ _ (.inr (.inr (congrArg Prod.snd src)))]
  have H (l : Link) (M : l∈links true) : some (0 : Fin 3)≠l.dst := by
    change l∈([⟨0,some 1⟩,⟨1,some 2⟩,⟨2,none⟩] : List Link) at M
    simp only [List.mem_cons,List.not_mem_nil,or_false] at M
    rcases M with A|A|A <;> subst l <;> decide
  rw [fold_right_frame _ _ _ _ _ _ _ _ _ H]
  exact nonparked_prefix_right_frame hu true u v 0 safe wire

theorem nonparked_prefix_trail_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : InboundToken (oldK hv v k)) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=(kField j).read u := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame (l : Link) (i : l∈pre) : j≠l.src := by
    have pw := links_distinct_src hv
    rw [L] at pw
    exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp))
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  rw [H,dst,nonparked_link_trail_guard _ _ _ _ _ _ _ _ _ trail safe,
    fold_left_frame _ _ _ _ _ _ _ _ _ A,←H,
    fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact prefix_left_trail_frame hu hv u v j trail u



#print axioms nonparked_inbound_frame_pair
#print axioms nonparked_root_inbound_frame_pair
#print axioms nonparked_prefix_trail_frame_pair
end L4.ShortResetRow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow

theorem fault_front_is_ready (hu : Bool) (u : BitVec 96) (j : Fin 3)
    (front : (oldK hu u j).tag=2) (F : (oldK hu u j).fault=true) :
    forwardReady hu u j=true := by
  simp [forwardReady,ready,parked,front,F]

theorem faultToken2_relay_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (F : oldK hu u j=faultToken 2) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode T ∧
      (kField k).read (q.2.apply v)=encode (faultToken 2) := by
  have R := fault_front_is_ready hu u j
    (congrArg Token.tag F) (congrArg Token.fault F)
  have S := forward_ready_out_pair hu hv u v j k dst R
  simpa [forwardPacket,F,effect,arrival,faultToken] using S

theorem faultToken2_terminal_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (dst : destination hv j=none) (F : oldK hu u j=faultToken 2) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=encode (faultToken 3) := by
  have R := fault_front_is_ready hu u j
    (congrArg Token.tag F) (congrArg Token.fault F)
  have S := forward_ready_turn_pair hu hv u v j dst R
  simpa [turnPacket,F,effect,terminal,faultToken] using S

#print axioms fault_front_is_ready
#print axioms faultToken2_relay_pair
#print axioms faultToken2_terminal_pair
end L4.ShortResetRow


namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow
open L4.MISByteRows (Link)

theorem parked_admit_inert_left_pair (hu hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (t : Token) (old : oldK hu u j=t) (tag : t.tag=2) (opcode : t.opcode=2)
    (live : t.fault=false) (gate : atGate hu u j=true)
    (race : t.race=3) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=(kField j).read u := by
  have P : parked t hu u j=true := by simp [parked,tag,opcode,live,gate]
  have lt : t.race<4 := by omega
  have norm : (t.race==1 || t.race==2)=false := by simp [race]
  have idle (win : Fin 3 → Bool) (p : Pair (Patch 96)) (d : Option (Fin 3)) :
      linkStep hu hv u v win p ⟨j,d⟩=p := by
    rcases p with ⟨a,b⟩
    simp [linkStep,old,ready,P,lt,tag]
  have pre_norm : (kField j).read ((rowPrefix (hu,hv) (u,v)).2.1.apply u)=
      (kField j).read u := by
    let normal := fun k : Fin 3 =>
      let z := oldK hu u k
      if z.fault then putK k z
      else if parked z hu u k && (z.race==1 || z.race==2) then putK k (raceNext z 3)
      else .empty _
    have selected : normal j=.empty _ := by
      dsimp only [normal]
      rw [old,live,P,norm]
      rfl
    have other (k : Fin 3) (N : j≠k) : Frames j (normal k) := by
      dsimp only [normal]
      split
      · exact fun z=>read_putK_other _ _ N _ z
      · split
        · exact fun z=>read_putK_other _ _ N _ z
        · exact empty_frames j
    let base := (if hu then
      grantsPatch (fun k => (canonical u k && !(hu && ready hu u k (oldK hu u k) &&
          !(oldK hu u k).fault && (oldK hu u k).opcode==0)) ||
        (rowPrefix (hu,hv) (u,v)).1 k)
      else ((resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)))
    change (kField j).read ((((base.compose (normal 0)).compose (normal 1)).compose (normal 2)).apply u)=_
    have js : j=0 ∨ j=1 ∨ j=2 := by
      have J := j.isLt
      have H : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
      rcases H with H|H|H
      · exact .inl (Fin.ext H)
      · exact .inr (.inl (Fin.ext H))
      · exact .inr (.inr (Fin.ext H))
    have base_hold : Frames j base := by
      dsimp [base]
      split
      · exact keep_high (by decide) _ _
      · exact compose_frames (compose_frames (keep_high (by decide) _ _)
          (keep_high (by decide) _ _)) (keep_high (by decide) _ _)
    rcases js with rfl|rfl|rfl
    · rw [Patch.compose_apply,(other 2 (by decide)),Patch.compose_apply,(other 1 (by decide)),
        Patch.compose_apply,selected,empty_frames,base_hold]
    · rw [Patch.compose_apply,(other 2 (by decide)),Patch.compose_apply,selected,
        empty_frames,Patch.compose_apply,(other 0 (by decide)),base_hold]
    · rw [Patch.compose_apply,selected,empty_frames,Patch.compose_apply,(other 1 (by decide)),
        Patch.compose_apply,(other 0 (by decide)),base_hold]
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame (l : Link) (i : l∈pre) : j≠l.src := by
    have pw := links_distinct_src hv
    rw [L] at pw
    exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp))
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  rw [idle,fold_left_frame _ _ _ _ _ _ _ _ _ A,
    fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact pre_norm

theorem parked_admit_inert_right_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (upstream : (oldK hu u j).tag≠2)
    (t : Token) (old : oldK hv v k=t) (tag : t.tag=2) (opcode : t.opcode=2)
    (live : t.fault=false) (gate : atGate hv v k=true)
    (race : t.race≠1 ∧ t.race≠3) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=(kField k).read v := by
  have P : parked t hv v k=true := by simp [parked,tag,opcode,live,gate]
  have norm : (t.race==1 || t.race==3)=false := by simp [race.1,race.2]
  have idle (win : Fin 3 → Bool) (p : Pair (Patch 96)) :
      linkStep hu hv u v win p ⟨j,some k⟩=p := by
    rcases p with ⟨a,b⟩
    simp [linkStep,old,ready,upstream,tag]
  have pre_norm : (kField k).read ((rowPrefix (hu,hv) (u,v)).2.2.apply v)=
      (kField k).read v := by
    rw [parked_right_norm,parkedNeighborBits,old,live,P,norm]
    rfl
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k link)
  have pre_frame (a : Link) (i : a∈pre) : some k≠a.dst := by
    have pw := links_distinct_dst hv
    rw [L] at pw
    have K := (List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp)
    rw [link] at K
    exact Ne.symm K
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [link,idle,fold_right_frame _ _ _ _ _ _ _ _ _ (Z k link),
    fold_right_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact pre_norm

theorem live_prefix_trail_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (trail : oldK hu u j=T)
    (safe : (oldK hv v k).tag=1 ∨ (oldK hv v k).tag=2) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField j).read (q.1.apply u)=(kField j).read u := by
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,A,_⟩ := link_split hv j
  have pre_frame (l : Link) (i : l∈pre) : j≠l.src := by
    have pw := links_distinct_src hv
    rw [L] at pw
    exact Ne.symm ((List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp))
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,rowPost_left]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  obtain ⟨a,b,H⟩ : ∃ a b, p=(a,b) := ⟨p.1,p.2,rfl⟩
  change (kField j).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).1.apply u)=_
  have hold : linkStep hu hv u v pr.1 (a,b) ⟨j,some k⟩=(a,b) := by
    rcases safe with S | S <;> simp [linkStep,trail,ready,T,S]
  rw [H,dst,hold,
    fold_left_frame _ _ _ _ _ _ _ _ _ A,←H,
    fold_left_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact prefix_left_trail_frame hu hv u v j trail u



theorem ungated_admit_inbound_frame_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (link : destination hv j=some k) (upstream : (oldK hu u j).tag≠2)
    (t : Token) (old : oldK hv v k=t) (tag : t.tag=2) (_opcode : t.opcode=2)
    (live : t.fault=false) (gate : atGate hv v k=false) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=(kField k).read v := by
  have P : parked t hv v k=false := by simp [parked,gate]
  have idle (win : Fin 3 → Bool) (p : Pair (Patch 96)) :
      linkStep hu hv u v win p ⟨j,some k⟩=p := by
    rcases p with ⟨a,b⟩
    simp [linkStep,old,ready,upstream,tag]
  have pre_norm : (kField k).read ((rowPrefix (hu,hv) (u,v)).2.2.apply v)=
      (kField k).read v := by
    rw [parked_right_norm,parkedNeighborBits,old,live,P]
    rfl
  rw [←localRow_eq]
  obtain ⟨pre,suf,L,_,Z⟩ := link_split hv j
  have post : hv=false ∨ k≠0 := by
    cases hv
    · exact .inl rfl
    · exact .inr (header_destination_ne_zero j k link)
  have pre_frame (a : Link) (i : a∈pre) : some k≠a.dst := by
    have pw := links_distinct_dst hv
    rw [L] at pw
    have K := (List.pairwise_append.mp pw).2.2 _ i ⟨j,destination hv j⟩ (by simp)
    rw [link] at K
    exact Ne.symm K
  unfold localRow
  dsimp only
  rw [L,List.foldl_append,List.foldl_cons,post_frame _ _ _ _ (post.imp_right .inl)]
  let pr := rowPrefix (hu,hv) (u,v)
  let p := pre.foldl (linkStep hu hv u v pr.1) pr.2
  change (kField k).read ((suf.foldl (linkStep hu hv u v pr.1)
      (linkStep hu hv u v pr.1 p ⟨j,destination hv j⟩)).2.apply v)=_
  rw [link,idle,fold_right_frame _ _ _ _ _ _ _ _ _ (Z k link),
    fold_right_frame _ _ _ _ _ _ _ _ _ pre_frame]
  exact pre_norm

theorem live_root_inbound_frame_pair (hu : Bool) (u v : BitVec 96)
    (wait : get v 81 2 (by decide)=2)
    (op : get v 78 3 (by decide) < 7)
    (safe : (oldK true v 0).tag=1 ∨ (oldK true v 0).tag=2)
    (W : (oldK true v 0).fault=false) :
    let q := MISByteRows.row (hu,true) (u,v)
    (kField 0).read (q.2.apply v)=(kField 0).read v := by
  have src := source_wait_holds v (oldK true v 0) wait op safe
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [post_frame _ _ _ _ (.inr (.inr (congrArg Prod.snd src)))]
  have H (l : Link) (M : l∈links true) : some (0 : Fin 3)≠l.dst := by
    change l∈([⟨0,some 1⟩,⟨1,some 2⟩,⟨2,none⟩] : List Link) at M
    simp only [List.mem_cons,List.not_mem_nil,or_false] at M
    rcases M with A|A|A <;> subst l <;> decide
  rw [fold_right_frame _ _ _ _ _ _ _ _ _ H]
  rw [parked_right_norm,parkedNeighborBits,W]
  have G : parked (oldK true v 0) true v 0=false := by simp [parked,atGate]
  rw [G]
  rfl

#print axioms parked_admit_inert_left_pair
#print axioms parked_admit_inert_right_pair
#print axioms live_prefix_trail_frame_pair
#print axioms ungated_admit_inbound_frame_pair
#print axioms live_root_inbound_frame_pair
end L4.ShortResetRow

namespace L4.ShortResetRow
open AllSizeProtocol MISByteCodec ShortResetFlow

theorem parked_outgoing_empty_pair (hu hv : Bool) (u v : BitVec 96) (j k : Fin 3)
    (dst : destination hv j=some k) (t : Token) (old : oldK hu u j=t)
    (tag : t.tag=2) (op : t.opcode=2) (live : t.fault=false)
    (gate : atGate hu u j=true) (race : t.race<4)
    (right : oldK hv v k=E) (wire : (kField k).read v=encode E) :
    let q := MISByteRows.row (hu,hv) (u,v)
    (kField k).read (q.2.apply v)=encode E := by
  have N : forwardReady hu u j=false := by simp [forwardReady,ready,parked,old,tag,op,live,gate,race]
  dsimp only
  rw [parked_outgoing_successor_pair hu hv u v j k dst (by rw [old,tag]) N]
  simp [parkedNeighborBits,right,parked,E,wire]

#print axioms parked_outgoing_empty_pair
end L4.ShortResetRow
