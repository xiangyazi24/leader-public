import Leader.L4.BStarGeneratedOwner
import Leader.L4.BStarGeneratedBandScan

namespace L4.BStarGeneratedTapeCuts
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFixedRouting BStarGeneratedOwner BStarLongCommand BStarLongDoor
open BStarGeneratedBandScan BStarClearanceSource
open BStarResetChartTouch BStarResetChartService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem at_start {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base addr len x a w b) : Current hp base addr len x a := by
  cases G <;> assumption

theorem at_end {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base addr len x a w b) : Current hp base addr len (run x w) b := by
  induction G with
  | endpoint C => exact C
  | next _ _ _ ih => exact ih

/-- A split at a literal word boundary keeps both exact traces and
their shared controller mode. It never reruns the scheduler proof
or chooses an independently admissible route. -/
theorem split {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} (u v : List (Fin n))
    (T : GeneratedOwner hp base addr len x a (u++v) b) :
    ∃ m, GeneratedOwner hp base addr len x a u m ∧
      GeneratedOwner hp base addr len (run x u) m v b := by
  induction u generalizing x a with
  | nil => exact ⟨a,.endpoint (at_start hp T),T⟩
  | cons e u ih =>
    cases T with
    | next I E rest =>
      obtain ⟨m,G,H⟩ := ih rest
      exact ⟨m,.next I E G,H⟩

theorem idle_of_issue {base x : X} {addr : Nat → Pos n} {len : Nat} {m : Mode}
    (C : Current hp base addr len x m) (I : Issue (x (addr 0).1).long) : m=.idle := by
  cases m with
  | idle => rfl
  | busy op z =>
    exact False.elim ((by decide : (2:Nat)≠1) (C.1.2.2.1.symm.trans I.2))

theorem root_cuts {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x) (closed : ∀ y e,Q y → Q (step y e))
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (w : List (Fin n)) :
    oldH6 B (run x w) (S.getD 0 fall).1=true ∧ (S.getD 0 fall).2=0 := by
  have keep (x : X) (w : List (Fin n)) (J : Q x) : Q (run x w) := by
    induction w generalizing x with
    | nil => exact J
    | cons e w ih => exact ih _ (closed _ e J)
  exact root_header hp C (fiber _ (keep _ _ I))

/-- A foreign-only segment of a generated idle owner stays idle
at every actual prefix, including the marks between ready411 and
its proper issuing door. -/
theorem idle_foreign_prefix {base x : X} {addr : Nat → Pos n} {len : Nat}
    {b : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base addr len x .idle w b)
    (foreign : ∀ e∈w,rightNeighbor e≠(addr 0).1)
    (u v : List (Fin n)) (W : w=u++v) :
    Current hp base addr len (run x u) .idle := by
  subst w
  induction u generalizing x with
  | nil => exact at_start hp T
  | cons e u ih =>
    cases T with
    | next I E rest =>
      have F := foreign e List.mem_cons_self
      cases E with
      | idle_hold away =>
        exact ih rest (fun f hf => foreign f (List.mem_cons_of_mem _ hf))
      | bad_issue own bad =>
        exact (F (own ▸ RearTrace.right_predecessor (addr 0).1)).elim
      | launch own L =>
        exact (F (own ▸ RearTrace.right_predecessor (addr 0).1)).elim

end L4.BStarGeneratedTapeCuts
