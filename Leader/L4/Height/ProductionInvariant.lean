import Leader.L4.Height.ProductionCustody
import Leader.L4.Height.ProductionReference

namespace L4.Height.ProductionCustody
open AllSizeProtocol PhysicalCustody BStarTrace BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting
open BStarAcquireRailCoverage BStarSteeredLikelihood
open Classical

private theorem frame_geometry {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (y : Raw s n) (qy : g.Q y) (i : Fin n) :
    (let G := longGeometry (rows s) (y i); (!G.axes.h6 || G.inside)=true) ∧
    (let G := oldPair (rows s) y i; continuation G.1 G.2=true) := by
  let b := rows s
  have hd (u : Fin n) : (longGeometry b (g.base u)).axes.h6=(longGeometry b (y u)).axes.h6 :=
    congrArg Prod.fst (g.fiber y qy u)
  have inside (u : Fin n) : (longGeometry b (g.base u)).inside=(longGeometry b (y u)).inside :=
    congrArg (fun t : Bool×Bool×Bool => t.2.1) (g.fiber y qy u)
  have last (u : Fin n) : (longGeometry b (g.base u)).last=(longGeometry b (y u)).last :=
    congrArg (fun t : Bool×Bool×Bool => t.2.2) (g.fiber y qy u)
  have one := g.heads i
  have two := g.cont i
  change (!(longGeometry b (g.base i)).axes.h6 || (longGeometry b (g.base i)).inside)=true at one
  rw [hd,inside] at one
  change continuation (longGeometry b (g.base i)) (longGeometry b (g.base (rightNeighbor i)))=true at two
  unfold continuation at two
  rw [inside,last,hd,inside] at two
  exact ⟨one,two⟩

/-- The actual successor relation is carried on the *same credited chart*
at the certified reference. The old reference offset need not be inferred
from layout equality. The original recovery tape is retained. -/
def OwnerFrame {s n : Nat} {x : Raw s n} (g : CustodyWitness x) (y : Raw s n)
    (a : Word n) (o : Owners (oldH6 (rows s) g.base)) : Prop :=
  ∃ (hh : ∃ j,oldH6 (rows s) g.initial j=true) (oi : Owners (oldH6 (rows s) g.initial))
    (pre mid tail : Word n) (S : List (Pos n)) (len : Nat) (fall : Pos n) (m : Mode),
    oi.val=o.val ∧ g.u++g.v=pre++mid++tail ∧
    BStarOwnerRecoveryPass.Recovered (show 0<2 by decide) g.base g.hh o (rawRun g.initial pre) mid ∧
    Chart (show 0<2 by decide) g.initial hh oi S len fall ∧
    BStarClearanceOffset.correct (oldH6 (rows s) g.initial) hh 5 g.initial ∧
    let addr := fun j => S.getD j fall
    let z := rawRun (rawRun g.initial pre) mid
    (BStarLongDoor.ctrlOp.read (z (addr 0).1).long).toNat=3 ∧
    GeneratedOwner (show 0<2 by decide) g.initial addr len z .idle (tail++(g.past++a)) m ∧
    Current (show 0<2 by decide) g.initial addr len y m ∧
    ∀ f, ∃ m', Event (show 0<2 by decide) addr len y f m m' ∧
      Current (show 0<2 by decide) g.initial addr len (rawNext s y f) m'

structure PhysicalInvariant {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (c : Word n → Fin n → Fin n) (i : Fin n) (y : History s n) : Prop where
  trace : Consistent x c i y
  ready : Ready g y.physical
  layout : ∀ j, Layout (rows s) g.initial j=Layout (rows s) y.physical j
  head : ∀ j, let G := longGeometry (rows s) (y.physical j); (!G.axes.h6 || G.inside)=true
  continuation : ∀ j, let G := oldPair (rows s) y.physical j; BStarAcquireRailCoverage.continuation G.1 G.2=true
  coherent : ∀ j,BStarLongGrant.conflict (BStarGrantReaderHistory.ports y.physical j)=false
  owners : ∀ o,OwnerFrame g y.physical y.emitted o

theorem invariant_of_consistent {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
    (P : Production g) (c : Word n → Fin n → Fin n) (i : Fin n) (y : History s n)
    (hc : Consistent x c i y) : PhysicalInvariant g c i y := by
  let hp : 0<2 := by decide
  have hy : Ready g y.physical := hc.2.1.symm ▸ ready_run P y.emitted
  have frame := g.fiber g.initial g.init
  have fixed (v : Raw s n) (q : g.Q v) (j : Fin n) :
      Layout (rows s) g.initial j = Layout (rows s) v j := (frame j).symm.trans (g.fiber v q j)
  refine ⟨hc,hy,fixed _ hy.1,fun j => (frame_geometry g _ hy.1 j).1,
    fun j => (frame_geometry g _ hy.1 j).2,g.coherent _ hy.1,?_⟩
  intro o
  obtain ⟨pre,mid,tail,S,len,fall,tape,recovered,C,pc,m,G,current⟩ :=
    generated_at_every_history P o y.emitted
  obtain ⟨hh',o',id,C'⟩ := ProductionReference.chart_on_reference hp C frame
  have heads : oldH6 (rows s) g.base=oldH6 (rows s) g.initial := funext fun j => congrArg Prod.fst (frame j)
  have offset : BStarClearanceOffset.correct (oldH6 (rows s) g.initial) hh' 5 g.initial := by
    have move {h k : Fin n → Bool} (H : h=k) (hh : ∃ j,h j=true) (hk : ∃ j,k j=true)
        (good : BStarClearanceOffset.correct h hh 5 g.initial) :
        BStarClearanceOffset.correct k hk 5 g.initial := by subst k; exact good
    exact move heads g.hh hh' g.offset
  have cur := ProductionReference.current_on_reference hp frame current
  rw [←hc.2.1] at cur
  refine ⟨hh',o',pre,mid,tail,S,len,fall,m,id,tape,recovered,C',offset,pc,
    ProductionReference.generated_on_reference hp frame G,cur,?_⟩
  intro f
  exact current_step hp C' g.Q fixed (fun v q e => g.closed v e q) (separation P) hy.1 f m cur

theorem production_inv {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
    (P : Production g) (c : Word n → Fin n → Fin n) (i : Fin n) (a : Word n) :
    PhysicalInvariant g c i (runWord (next c i) (start x) a) :=
  invariant_of_consistent P c i _ (run_consistent x c i _ (consistent_start x c i) a)

theorem invariant_closed {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
    (P : Production g) (c : Word n → Fin n → Fin n) (i : Fin n) (y : History s n)
    (hy : PhysicalInvariant g c i y) (e : Fin n) : PhysicalInvariant g c i (next c i y e) :=
  invariant_of_consistent P c i _ (consistent_next x c i y hy.trace e)

#print axioms production_inv
#print axioms invariant_closed
end L4.Height.ProductionCustody

namespace L4.Height.ProductionCycles
open AllSizeProtocol PhysicalCustody ProductionCustody BStarSteeredLikelihood BStarH6WordChart
open BStarAcquireAnchors BStarAcquireLiteralChain
variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base

/-- The incoming physical mark that moves an owner's source from RREL to ISSUE3. -/
def accepted (o : Owners h) (a : Word n) (e : Fin n) : Prop :=
  let root := (endpoint h g.hh o 0).1
  let old := rawRun x a
  e=RearTrace.predecessor root ∧ (BStarLongDoor.ctrlOp.read (old root).long).toNat=2 ∧
    (BStarLongDoor.ctrlOp.read (rawNext s old e root).long).toNat=3

end L4.Height.ProductionCycles

