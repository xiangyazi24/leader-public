import Leader.L4.BStarPublicCodec

/-! The public row uses the literal native pair for values and the
ordered field assignments for support, including identity writes. -/
namespace L4.BStarPublic
open AllSizeProtocol BStarPublicCodec

def pubMask {p c₁ : Nat} (x : Pair (Site p c₁)) : Pair (BitVec (publicWidth p c₁)) :=
  let W := publicWidth p c₁
  let q := ell (4*c₁+3)
  let lane := fun i k : Nat => BitVec.ofNat W ((2^k-1)*2^i)
  let rail := lane 0 3
  let src := lane 3 q
  let stock := lane (3+q) 1
  let sig := lane (4+q) 2
  let shield := lane (6+q) 1
  let bullet := lane (7+q) 2
  let leader := lane (9+q) 1
  let mark := lane (10+q) 1
  let res := lane (11+q) (ell p)
  let u := x.1
  let v := x.2
  let set := fun (b : Bool) (m : BitVec W) => if b then m else 0
  let f := fireInitiator (materialize u v)
  let g := fireResponder v
  let hit := !(f.bullet == .none) && g.leader
  let kill := hit && f.bullet == .live && !g.shield
  let (l,r) := impact f g
  let pin := pinned l r
  let send := !(l.bullet == .none) && !r.leader
  let (_,vN) := followerBullet pin l r
  let (uN,_) := native (materialize u v) v
  let pay := payer uN
  let passStock := !vN.leader && !uN.mark && !vN.stock && pay
  let passMark := !vN.leader && uN.mark && pay
  let mL := set (v.leader || u.mark || defect u v) mark |||
    set (u.leader && !(u.signal == .zero)) (bullet ||| shield ||| sig) |||
    set (hit || send) bullet ||| sig ||| set vN.leader (mark ||| stock) |||
    set passStock stock ||| set passMark (stock ||| mark)
  let mR := set (v.leader && !(v.signal == .zero)) (bullet ||| shield ||| sig) |||
    set kill leader ||| set (send && !pin) sig |||
    set (send && !pin && r.bullet == .none) bullet |||
    set passStock stock ||| set passMark (res ||| mark)
  let (a,b) := payment uN vN
  let root := b.leader || a.mark
  let pg := pinned a b
  let t : Patrol (2*c₁) := ⟨b.source,a.rail,b.rail,false⟩
  let s := sourceGuard pg t
  let mR := mR ||| set (!pg || t.source == .off) src |||
    set (!pg && !(t.source == .off)) rail
  let ar := arrivals root pg b.leader s
  let (ml,mr) : Pair (BitVec W) :=
    if s.left == .x && pg then (rail,src)
    else if s.left == .x && b.leader then (rail,0)
    else if s.source == .i1 && s.left == .di then (rail,src)
    else match s.source, s.left with
      | .await _, .dc => (rail,src)
      | _, _ => if root && returning s.left then (rail,0)
                else (0,set (waiting s.source && s.left == .e) src)
  let launching := match ar.source with | .i0 | .count _ => true | _ => false
  let z := launch ar
  let aTurn := root && (z.right == .ui || z.right == .uc || z.right == .t)
  let both := !root && (z.right == .ui || z.right == .uc ||
    returning z.left || z.left == .x)
  let rightOnly := !root && z.left == .e && z.right == .t
  (mL ||| ml ||| set (launching || both) rail,
   mR ||| mr ||| set launching src ||| set (aTurn || both || rightOnly) rail |||
     set (ar.fire && pg) (leader ||| bullet ||| shield ||| sig ||| src))

def publicWork {p c₁ : Nat} (hp : 0<p) (x : Pair (BitVec (publicWidth p c₁))) :
    Pair (Patch (publicWidth p c₁)) :=
  let u := Pair.map (readPub hp) x
  let y := L4.pairStep u.1 u.2
  let m := pubMask u
  (⟨m.1,packPub y.1⟩,⟨m.2,packPub y.2⟩)

/-- N5 assigns canonical left signal even on a decoded zero-to-zero
transition; the held spare bullet on that same edge remains raw 3. -/
theorem n5_identity_intent :
    let u : BitVec (publicWidth 3 12) := ((signalF 3 12).assign 3).apply
      (((bulletF 3 12).assign 3).apply 0)
    let v : BitVec (publicWidth 3 12) := ((residueF 3 12).assign 1).apply 0
    let patch := publicWork (p:=3) (c₁:=12) (by decide) (u,v)
    let y := patch.1.apply u
    (signalF 3 12).read y=0 ∧ (bulletF 3 12).read y=3 ∧
      (patch.1.mask.getLsbD (4+q 12))=true ∧
      (patch.1.mask.getLsbD (7+q 12))=false := by decide

end L4.BStarPublic
