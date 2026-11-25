import Leader.L4.BStarAcquireVisitOrder

/-! A fixed lower fiber freezes the structural command links. Packed
scratch and upper authority bytes may keep changing on the fiber. -/
namespace L4.BStarLongFixedRouting
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarCommandChronology
open BStarAcquireVisitOrder

def Layout {a : LargeParams} {n : Nat} (b : LargeRows a) (x : Fin n → LargeSite a)
    (i : Fin n) : Bool × Bool × Bool :=
  let g := longGeometry b (x i)
  (g.axes.h6,g.inside,g.last)

private def minimal (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

theorem command_eq {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x y : Fin n → LargeSite a)
    (same : ∀ i,Layout b x i=Layout b y i) (e : Fin n) :
    orderedCommands (oldPair b x e)=orderedCommands (oldPair b y e) := by
  let u := oldPair b x e
  let v := oldPair b y e
  have l := same e
  have r := same (rightNeighbor e)
  change (u.1.axes.h6,u.1.inside,u.1.last)=(v.1.axes.h6,v.1.inside,v.1.last) at l
  change (u.2.axes.h6,u.2.inside,u.2.last)=(v.2.axes.h6,v.2.inside,v.2.last) at r
  have LI : u.1.inside=v.1.inside := congrArg (fun z : Bool × Bool × Bool => z.2.1) l
  have LL : u.1.last=v.1.last := congrArg (fun z : Bool × Bool × Bool => z.2.2) l
  have RH : u.2.axes.h6=v.2.axes.h6 := congrArg Prod.fst r
  have RI : u.2.inside=v.2.inside := congrArg (fun z : Bool × Bool × Bool => z.2.1) r
  change orderedCommands u=orderedCommands v
  change select Claim.slots [] (offers commandKey (commandClaims u))=
    select Claim.slots [] (offers commandKey (commandClaims v))
  rw [show commandClaims u =
    commandClaims (minimal false u.1.inside u.1.last,minimal u.2.axes.h6 u.2.inside false) from rfl,
    show commandClaims v =
    commandClaims (minimal false v.1.inside v.1.last,minimal v.2.axes.h6 v.2.inside false) from rfl,
    LI,LL,RH,RI]

theorem edge_fixed {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x y : Fin n → LargeSite a)
    (same : ∀ i, Layout b x i=Layout b y i) (u v : Pos n) :
    Edge b x u v ↔ Edge b y u v := by
  constructor
  · rintro ⟨e,c,d,M,D,U,V⟩
    exact ⟨e,c,d,command_eq b x y same e ▸ M,D,U,V⟩
  · rintro ⟨e,c,d,M,D,U,V⟩
    exact ⟨e,c,d,(command_eq b x y same e).symm ▸ M,D,U,V⟩

#print axioms command_eq
#print axioms edge_fixed
end L4.BStarLongFixedRouting
