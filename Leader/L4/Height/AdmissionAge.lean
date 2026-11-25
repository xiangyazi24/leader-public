import Leader.L4.Height.ProductionAdmissions
import Leader.L4.Height.ServiceCustody
import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarSteeredLikelihood

namespace L4.Height.CandidateResidence
open PhysicalCustody BStarSteeredLikelihood
variable {s n : Nat}
local notation "hp" => (show 0<2 by decide)

/-- The last own launch on the emitted prefix issued ADMIT after the query.
All intervening old door rows are tested for a physical launch. -/
def newAdmission (origin : Raw s n) (root : Fin n) (a : Word n) : Prop :=
  ∃ u e v, a=u++e::v ∧ ProductionAdmissions.issues hp origin root u e ∧
    ∀ b f c, v=b++f::c →
      ¬(f=RearTrace.predecessor root ∧
        BStarClearanceSource.Launch (rawRun origin ((u++[e])++b) root).long
          (rawNext s (rawRun origin ((u++[e])++b)) f root).long)

open BStarOwnerLaunchOrigin BStarGeneratedOwner BStarAcquireVisitOrder BStarSeparatingRail
open BStarLongCommand BStarGeneratedTapeCuts

private theorem busy_cut {base y : Raw s n} {addr : Nat → Pos n} {len op : Nat}
    {z endC : Cursor} (u v : Word n)
    (H : BusyOnly hp base addr len op y z (u++v) endC) :
    ∃ k,Current hp base addr len (rawRun y u) (.busy op k) := by
  induction u generalizing z y with
  | nil => exact ⟨z,busy_start hp H⟩
  | cons f u ih =>
    cases H with
    | cons _ _ rest => exact ih rest

def Classified {s n : Nat} (base y : Raw s n) (addr : Nat → Pos n) (len : Nat)
    (m : Mode) (a : Word n) (endC : Cursor) : Prop :=
  (newAdmission y (addr 0).1 a ∧ Found hp base addr len admit y a endC) ∨
  (¬newAdmission y (addr 0).1 a ∧ ∃ z,m=.busy admit z ∧ BusyOnly hp base addr len admit y z a endC)

/-- Every in-flight ADMIT on the actual emitted word has exactly the
appropriate launch age, including an in-flight request at the query cut. -/
theorem admission_age {base y : Raw s n} {addr : Nat → Pos n} {len : Nat}
    {m : Mode} {a : Word n} {endC : Cursor}
    (G : GeneratedOwner hp base addr len y m a (.busy admit endC)) :
    Classified base y addr len m a endC := by
  rcases extract hp G with F|⟨z,eq,B⟩
  · refine .inl ⟨?_,F⟩
    obtain ⟨u,v,e,tape,door,launch,pc,run⟩ := F
    refine ⟨u,e,v,tape,⟨door,launch,pc⟩,?_⟩
    intro b f c cut bad
    subst v
    obtain ⟨k,cur⟩ := busy_cut b (f::c) run
    have now : rawRun y ((u++[e])++b)=rawRun (rawNext s (rawRun y u) e) b :=
      (BStarResetSchedule.run_append (rawNext s) y (u++[e]) b).trans
        (congrArg (fun z => rawRun z b) (BStarResetSchedule.run_append (rawNext s) y u [e]))
    have issue := bad.2.1
    rw [now] at issue
    cases idle_of_issue hp cur issue
  · refine .inr ⟨?_,z,eq,B⟩
    rintro ⟨u,e,v,cut,hit,_⟩
    subst a
    obtain ⟨k,cur⟩ := busy_cut u (e::v) B
    cases idle_of_issue hp cur hit.2.1.1

end L4.Height.CandidateResidence

