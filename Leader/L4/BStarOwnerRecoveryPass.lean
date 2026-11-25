import Leader.L4.BStarRecoveryPass
import Leader.L4.BStarClearanceAfterSeparator
import Leader.L4.BStarGrantBirth

namespace L4.BStarOwnerRecoveryPass
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetSchedule BStarSeparatingRail
open BStarSeparatorControl BStarClearanceSource BStarClearanceOffset
open BStarResetHealthyCycle BStarLongDoor BStarLongCommand

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- A segment witnesses a genuine separating launch and return, then
three later healthy reset stages. No grant cleanliness is built into
this event by definition. -/
def Recovered (base : X) (hh : ∃ i,oldH6 B base i=true)
    (o : Owners (oldH6 B base)) (x : X) (w : List (Fin n)) : Prop :=
  ∃ (S : List (Pos n)) (len : Nat) (fall : Pos n), Chart hp base hh o S len fall ∧
    ∃ (u v residual w₀ w₁ w₂ : List (Fin n)) (y₁ y₂ : X),
      let addr := fun j => S.getD j fall
      let root := (addr 0).1
      let door := RearTrace.predecessor root
      let before := BStarResetSchedule.run step x u
      let launched := step before door
      let returned := BStarResetSchedule.run step launched v
      let consumed := step returned door
      let zero := BStarResetSchedule.run step consumed residual
      w=u ++ (door::(v++[door])) ++ residual ++ w₀ ++ w₁ ++ w₂ ∧
        Launch (before root).long (launched root).long ∧
        Seen step (project addr) anyTag len launched (.out 0) v (.back 0) ∧
        Clean (project addr) anyTag len returned ∧
        Stage hp addr len 0 zero w₀ y₁ ∧ Stage hp addr len 1 y₁ w₁ y₂ ∧
        Stage hp addr len 2 y₂ w₂ (BStarResetSchedule.run step x w)

/-- Produce two ordered passes of actual recovery segments for all owners
in the supplied list. The second pass is wholly after completion of the
first. This is a statement about physical histories, not yet the
two authority invariants at their cut times. -/
theorem two_recoveries {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (charts : ∀ o : Owners (oldH6 B base), ∃ S len fall, Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (same : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base)
    (owners : List (Owners (oldH6 B base))) (I : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    let Inv := fun z => Q z ∧ correct (oldH6 B base) hh 5 z
    let E := Recovered hp base hh
    ∃ u v, Inv (BStarResetSchedule.run step x u) ∧ Inv (BStarResetSchedule.run step x (u++v)) ∧
      (∀ o∈owners, ∃ a b, a<b ∧ b≤u.length ∧ BStarRecoveryPass.Credit step E o x (u++v) a b) ∧
      (∀ o∈owners, ∃ a b, u.length≤a ∧ a<b ∧ BStarRecoveryPass.Credit step E o x (u++v) a b) := by
  dsimp only
  let Inv := fun z => Q z ∧ correct (oldH6 B base) hh 5 z
  have force (o : Owners (oldH6 B base)) (z : X) (J : Inv z) :
      ∃ q, 0<q.length ∧ Inv (BStarResetSchedule.run step z q) ∧ Recovered hp base hh o z q := by
    obtain ⟨S,len,fall,chart⟩ := charts o
    obtain ⟨u,_,v,residual,w₀,w₁,w₂,_,y₁,y₂,y₃,L,_,A,C,_,_,_,_,_,T₀,T₁,T₂,E,H,K,_,_,_,_⟩ :=
      BStarClearanceAfterSeparator.reach_clean_after_resets hp chart sep head cont
        Q closed same heads conts cb J.1 J.2
    let door := RearTrace.predecessor (S.getD 0 fall).1
    let q := u ++ (door::(v++[door])) ++ residual ++ w₀ ++ w₁ ++ w₂
    have eq : BStarResetSchedule.run step z q=y₃ := E
    refine ⟨q,by simp [q]; omega,by rw [eq]; exact ⟨H,K⟩,?_⟩
    refine ⟨S,len,fall,chart,u,v,residual,w₀,w₁,w₂,y₁,y₂,rfl,L,A,C,T₀,T₁,?_⟩
    rw [eq]
    exact T₂
  exact BStarRecoveryPass.two_pass step force force owners x ⟨I,cx⟩

open BStarGrantBirth

/-- Lift a reset endpoint's actual zero grant to the cut's common
history. A live grant at the cut has an old winning mark after that
owner's credited reset, and stays continuously held from that mark.
This is bit provenance, not yet the protected-bank theorem. -/
theorem credit_grant {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {w : List (Fin n)} {a b : Nat}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (credit : BStarRecoveryPass.Credit step (Recovered hp base hh) o x w a b)
    (i : Fin n) (j : Fin 3) (Q : X → Prop)
    (closed : ∀ z e,Q z → Q (step z e)) (init : Q x)
    (zero_at_reset : ∀ z q, Q z → Recovered hp base hh o z q →
      bit (BStarResetSchedule.run step z q) i j=0)
    (live : bit (BStarResetSchedule.run step x w) i j≠0) :
    ∃ lead e tail, w=lead++e::tail ∧ b≤lead.length ∧
      let before := BStarResetSchedule.run step x lead
      bit before i j=0 ∧ WonAt hp before e i j ∧ Continuous hp (step before e) i j tail := by
  obtain ⟨pre,mid,post,W,_,timeEq,R⟩ := credit
  have preserved (v : List (Fin n)) (z : X) (T : Q z) : Q (BStarResetSchedule.run step z v) := by
    induction v generalizing z with
    | nil => exact T
    | cons e v ih => exact ih _ (closed z e T)
  let u := pre++mid
  have W' : w=u++post := W
  have I : bit (BStarResetSchedule.run step x u) i j=0 := by
    change bit (BStarResetSchedule.run step x (pre++mid)) i j=0
    rw [BStarResetSchedule.run_append]
    exact zero_at_reset _ _ (preserved pre x init) R
  rw [W',BStarResetSchedule.run_append] at live
  obtain ⟨p,e,t,T,Z,A,K⟩ := born_after_zero hp sep _ i j post I live
  refine ⟨u++p,e,t,by simp [W',T,List.append_assoc],?_,?_⟩
  · rw [List.length_append]
    change b≤(pre++mid).length+p.length
    omega
  · rw [BStarResetSchedule.run_append]
    exact ⟨Z,A,K⟩

end L4.BStarOwnerRecoveryPass
