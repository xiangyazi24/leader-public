import Leader.L4.BStarBitFullService

namespace L4.BStarNeedServicePlan
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarLongFixedRouting BStarClearanceRaceMark BStarAcquireRailCoverage

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def Forward (base : X) (addr : Nat→Pos n) (len a : Nat) (w : List (Fin n)) : Prop :=
  ∀ j (J : j<w.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
    linkAt hp y w[j] addr len (a+j)

def Reverse (base : X) (addr : Nat→Pos n) (len : Nat) (w : List (Fin n)) : Prop :=
  ∀ j (J : j<w.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
    linkAt hp y w[j] addr len (w.length-(j+1))

structure Plan (base : X) (addr : Nat→Pos n) (len k g : Nat) where
  out409 : List (Fin n)
  beforeBit : List (Fin n)
  afterBit : List (Fin n)
  back : List (Fin n)
  out411 : List (Fin n)
  turn : Fin n
  size409 : k+1+out409.length=len
  sizeBefore : beforeBit.length=g
  sizeAfter : g+1+afterBit.length=len
  sizeBack : back.length=len
  size411 : out411.length=k
  nom409 : Forward hp base addr len (k+1) out409
  nomBefore : Forward hp base addr len 0 beforeBit
  nomAfter : Forward hp base addr len (g+1) afterBit
  nomBack : Reverse hp base addr len back
  nom411 : Forward hp base addr len 0 out411
  nomTurn : ∀ y : X, (∀ i,Layout B base i=Layout B y i)→onTerminal hp y turn addr len

def sealWord {base : X} {addr : Nat→Pos n} {len k g : Nat} (P : Plan hp base addr len k g) :
    List (Fin n) :=
  (P.out409++[P.turn])++(P.back++[RearTrace.predecessor (addr 0).1])

def bitWord {base : X} {addr : Nat→Pos n} {len k g : Nat} (P : Plan hp base addr len k g) (i : Fin n) :
    List (Fin n) :=
  RearTrace.predecessor (addr 0).1 ::
    (P.beforeBit++([incident i .left,incident i .right,incident i .left]++
      (P.afterBit++P.turn::(P.back++[RearTrace.predecessor (addr 0).1]))))

def commitWord {base : X} {addr : Nat→Pos n} {len k g : Nat} (P : Plan hp base addr len k g) (i : Fin n) :
    List (Fin n) :=
  RearTrace.predecessor (addr 0).1::(P.out411++[i])

def service {base : X} {addr : Nat→Pos n} {len k g : Nat} (P : Plan hp base addr len k g)
    (center gateSite : Fin n) : List (Fin n) :=
  sealWord hp P++(bitWord hp P gateSite++commitWord hp P center)

theorem service_length {base : X} {addr : Nat→Pos n} {len k g : Nat} (P : Plan hp base addr len k g)
    (center gateSite : Fin n) : (service hp P center gateSite).length=4*len+8 := by
  simp only [service,sealWord,bitWord,commitWord,List.length_append,List.length_cons,List.length_nil,P.sizeBack,
    P.size411,P.sizeBefore]
  have A := P.size409
  have D := P.sizeAfter
  omega

/-- The complete nominal word depends only on the fixed layout and chart,
not on physical packet values or on any future raw samples. -/
theorem plan_exists {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (k g : Nat) (K : k<len) (G : g<len) :
    Nonempty (Plan hp base (fun j=>S.getD j fall) len k g) := by
  obtain ⟨A,AS,AN⟩ := BStarBitFullService.nominate_forward hp C head cont (len-(k+1)) (k+1) (by omega)
  obtain ⟨B1,BS,BN⟩ := BStarBitFullService.nominate_forward hp C head cont g 0 (by omega)
  obtain ⟨C1,CS,CN⟩ := BStarBitFullService.nominate_forward hp C head cont (len-(g+1)) (g+1) (by omega)
  obtain ⟨D,DS,DN⟩ := BStarReplyService.nominate_back hp C head cont len (Nat.le_refl _)
  obtain ⟨E,ES,EN⟩ := BStarBitFullService.nominate_forward hp C head cont k 0 (by omega)
  obtain ⟨t,T⟩ := BStarBitPositiveTerminal.nominate_terminal hp C head cont
  exact ⟨⟨A,B1,C1,D,E,t,by omega,BS,by omega,DS,ES,AN,BN,CN,DN,EN,T⟩⟩

#print axioms service_length
#print axioms plan_exists
end L4.BStarNeedServicePlan
