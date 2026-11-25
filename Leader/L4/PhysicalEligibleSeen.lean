import Leader.L4.PhysicalEligibleReply

namespace L4.PhysicalEligibleReply
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarAcquireForwardTrace BStarResetChartTouch
open BStarResetChartService BStarResetMarkAdapter BStarResetRailRing
open BStarResetSchedule BStarSeparatingRail BStarAcquireWaitControl
open BStarResetCycle BStarResetHealthyService BStarGeneratedOwner BStarClearanceSource
open BStarResetChartNomination BStarSeparatingProgress BStarAcquireRailCoverage
local notation "hp" => (show 0<2 by decide)

/-- The accepted healthy Seen induction itself supplies the matching
old reply and the whole suffix, together with literal waiting PC and
phase. No additional eligibility hypothesis is needed at back zero. -/
theorem eligible_of_seen {s n : Nat} {base y : Raw s n} {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e))
    (H : op<3) (qy : Q y) (F : Launched base (fun j=>S.getD j fall) len op y)
    (w : List (Fin n))
    (path : Seen (rawNext s) (project (fun j=>S.getD j fall)) (healthyTag op) len
      y (.out 0) w (.back 0)) :
    Q (rawRun y w) ∧ Eligible base (fun j=>S.getD j fall) len op (rawRun y w) := by
  let addr := fun j=>S.getD j fall
  have fold {x : Raw s n} {u v : Cursor} {t : List (Fin n)}
      (P : Seen (rawNext s) (project addr) (healthyTag op) len x u t v) :
      Q x → Waiting hp base (addr 0).1 op x → Good (healthyTag op) len (project addr x) u →
      Q (rawRun x t) ∧ Waiting hp base (addr 0).1 op (rawRun x t) ∧
        Good (healthyTag op) len (project addr (rawRun x t)) v := by
    induction P with
    | nil _ _ => exact fun a b c=>⟨a,b,c⟩
    | @cons x e w c d f live _ _ newGood tail ih =>
      intro q wait oldGood
      have qq := closed _ e q
      have next := waiting_closed_at hp C e op H (fiber _ qq) c live (weak_good _ _ _ _ oldGood) wait
      exact ih qq next newGood
  have g : Good (healthyTag op) len (project addr y) (.out 0) :=
    ⟨Nat.zero_le _,F.2,fun j J=>(Nat.not_lt_zero j J).elim⟩
  obtain ⟨q,ready,done⟩ := fold path qy F.1.1 g
  exact ⟨q,ready,⟨done.2.1,done.2.2.2⟩,done.2.1⟩

end L4.PhysicalEligibleReply
