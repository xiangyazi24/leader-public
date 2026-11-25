import Leader.L4.BStarRecoveredHistory
import Leader.L4.BStarClearanceOffsetMask

namespace L4.Height.ProductionReference
open AllSizeProtocol BStarLongWork BStarTrace BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors
open BStarAcquireLiteralChain BStarResetChartTouch BStarAcquireRailCoverage
open BStarLongFixedRouting BStarGeneratedOwner

private theorem endpoint_transport {n : Nat} {h k : Fin n → Bool} (same : h=k)
    {hh : ∃ i,h i=true} {hk : ∃ i,k i=true} {o : Owners h} {p : Owners k}
    (id : o.val=p.val) (j : Fin 11) : endpoint h hh o j=endpoint k hk p j := by
  subst k
  have eq : o=p := Subtype.ext id
  cases eq
  rfl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem chart_on_reference {base ref : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (old : Chart hp base hh o S len fallback) (frame : ∀ i, Layout B base i=Layout B ref i) :
    ∃ (hh' : ∃ i,oldH6 B ref i=true) (o' : Owners (oldH6 B ref)),
      o'.val=o.val ∧ Chart hp ref hh' o' S len fallback := by
  have h : oldH6 B base=oldH6 B ref := funext (fun i => congrArg Prod.fst (frame i))
  let hh' : ∃ i,oldH6 B ref i=true := by rw [←h]; exact hh
  let o' : Owners (oldH6 B ref) := ⟨o.val,by rw [←h]; exact o.property⟩
  have act (v : Pos n) : active (longGeometry B (base v.1)) v.2 =
      active (longGeometry B (ref v.1)) v.2 := by
    have inside := congrArg (fun m : Bool×Bool×Bool => m.2.1) (frame v.1)
    unfold active
    rw [show (longGeometry B (base v.1)).inside=(longGeometry B (ref v.1)).inside from inside]
  refine ⟨hh',o',rfl,old.length,old.nodup,old.root.trans (endpoint_transport h rfl 0),
    old.terminal.trans (endpoint_transport h rfl 10),?_,?_,?_⟩
  · intro v hv own
    exact old.cover v ((act v).trans hv) ((congrArg (fun t => commandOwner t v.1 v.2) h).trans own)
  · intro v hv
    obtain ⟨a,b⟩ := old.entries v hv
    exact ⟨(act v).symm.trans a,(congrArg (fun t => commandOwner t v.1 v.2) h).symm.trans b⟩
  · intro u v mem edge
    exact old.edge u v mem ((edge_fixed B base ref frame u v).mpr edge)

theorem current_on_reference {base ref x : X} {addr : Nat → Pos n} {len : Nat} {m : Mode}
    (frame : ∀ i,Layout B base i=Layout B ref i) (cur : Current hp base addr len x m) :
    Current hp ref addr len x m := by
  cases m with
  | idle => exact cur
  | busy op cursor =>
    exact ⟨⟨fun i => (frame i).symm.trans (cur.1.1 i),cur.1.2⟩,cur.2⟩

theorem generated_on_reference {base ref x : X} {addr : Nat → Pos n} {len : Nat} {m d : Mode}
    {w : List (Fin n)} (frame : ∀ i,Layout B base i=Layout B ref i)
    (G : GeneratedOwner hp base addr len x m w d) : GeneratedOwner hp ref addr len x m w d := by
  induction G with
  | endpoint cur => exact .endpoint (current_on_reference hp frame cur)
  | next cur E _ ih => exact .next (current_on_reference hp frame cur) E ih

end L4.Height.ProductionReference

