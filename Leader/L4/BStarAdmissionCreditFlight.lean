import Leader.L4.BStarParkedSteering
import Leader.L4.BStarCommitNoPrior

namespace L4.BStarAdmissionCreditFlight
open AllSizeProtocol BStarTrace BStarLongWork BStarLongCommand BStarLongToken BStarLongDoor
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart BStarGeneratedOwner
open BStarSeparatingRail BStarResetMarkAdapter BStarOwnerLaunchOrigin BStarCommitNoPrior
open BStarAcquireHistorySample BStarOwnerControlHistory BStarClearanceSource BStarAcquireForwardTrace
open BStarAdmitIncidentGeometry BStarParkedSteering BStarClearanceRaceMark BStarLongClaims BStarH6Ordinal
open BStarSteeredLikelihood
set_option maxRecDepth 4096

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- Literal old source door and actual launch; same predicate as
ProductionAdmissions.issues (no eligibility presumed at the remote gate). -/
def genuineIssue (ini : X) (root : Fin n) (a : Word n) (e : Fin n) : Prop :=
  let x := run ini a
  e=RearTrace.predecessor root ∧ Launch (x root).long (step x e root).long ∧
    (ctrlOp.read (x root).long).toNat=admit

private theorem busy_cut {base x : X} {addr : Nat→Pos n} {len op : Nat} {z d : Cursor}
    (u v : Word n) (P : BusyOnly hp base addr len op x z (u++v) d) :
    ∃ q, BusyOnly hp base addr len op (run x u) q v d := by
  induction u generalizing x z with
  | nil => exact ⟨z,P⟩
  | cons e u ih =>
    cases P with
    | cons _ _ tail => exact ih tail

theorem before_arrival_no_front {base x : X} {addr : Nat→Pos n} {len k j : Nat}
    {z : Cursor} (w u v : Word n) (D : w=u++v)
    (P : BusyOnly hp base addr len admit x z w (.out j)) (J : j<k) (K : k≤len) :
    ¬∃ q,project addr (run x u) k=.forward q := by
  subst w
  obtain ⟨q,Bq⟩ := busy_cut hp u v P
  obtain ⟨i,I⟩ := busy_no_back_to_out hp Bq ⟨j,rfl⟩
  subst q
  have Ij := outward_mono hp Bq i j rfl rfl
  have now := busy_start hp Bq
  intro F
  have eq := (pointed_unique_forward (project addr (run x u)) len i now.2.1 now.2.2 k K).mp F
  omega

/-- An eligible old prefix is charged only on one of the gate's incident labels. -/
def physicalHit {n : Nat} (gate : Fin n) (live : Word n → Prop)
    (a : Word n) (e : Fin n) : Prop :=
  live a ∧ ∃ s, e=incident gate s

/-- Only two recurrences are needed: a genuine launch sets the credit,
and a credited non-hit preserves it. No assumptions on unrelated states. -/
theorem monitor_after_launch {n : Nat}
    (credit : Word n → Bool) (hit : Word n → Fin n → Prop)
    (a : Word n) (launch : Fin n) (w : Word n)
    (funded : credit (a++[launch])=true)
    (preserve : ∀ b e, credit b=true → ¬hit b e → credit (b++[e])=true)
    (untouched : ∀ u f v, w=u++f::v → ¬hit ((a++[launch])++u) f) :
    credit ((a++[launch])++w)=true := by
  have keep (p t : Word n) (b : credit p=true)
      (no : ∀ u f v, t=u++f::v → ¬hit (p++u) f) : credit (p++t)=true := by
    induction t generalizing p with
    | nil => simpa using b
    | cons f v ih =>
      have off : ¬hit p f := by simpa using no [] f v rfl
      have later (u : Word n) (j : Fin n) (z : Word n) (eq : v=u++j::z) :
          ¬hit ((p++[f])++u) j := by
        simpa only [List.append_assoc,List.singleton_append,List.nil_append] using
          no (f::u) j z (congrArg (List.cons f) eq)
      simpa only [List.append_assoc,List.singleton_append,List.nil_append] using
        ih _ (preserve _ _ b off) later
  exact keep _ _ funded untouched

/-- No credit is spent before an actual admission reaches K1: the
proper-prefix cursor is still strictly before the gate, even if those
physical marks use one of the future gate's edge labels. The arrival
mark reads its old state. Once arrived, arbitrary offsite emitted marks
preserve the same credit. -/
theorem credit_through_arrival {base x : X} {addr : Nat→Pos n} {len k j : Nat}
    (a u quiet : Word n) (launch arrival : Fin n) (gate : Fin n)
    (I : genuineIssue hp x (addr 0).1 a launch)
    (P : BusyOnly hp base addr len admit (step (run x a) launch) (.out 0) u (.out j))
    (J : j<k) (K : k≤len)
    (live : Word n→Prop)
    (sound : ∀ b,live b → ∃ q,project addr (run x b) k=.forward q)
    (credit : Word n → Bool)
    (sets : genuineIssue hp x (addr 0).1 a launch → credit (a++[launch])=true)
    (preserve : ∀ b e, credit b=true → ¬physicalHit gate live b e →
      credit (b++[e])=true)
    (offsite : ∀ e∈quiet,∀ s,e≠incident gate s) :
    credit ((a++[launch])++(u++arrival::quiet))=true := by
  apply monitor_after_launch credit (physicalHit gate live) a launch _ (sets I) preserve
  intro pre e post W hit
  have M : ∀ b f z,u=b++f::z → ¬live ((a++[launch])++b) := by
    intro b f z D H
    have F := sound _ H
    rw [BStarResetSchedule.run_append, BStarResetSchedule.run_append step x a [launch]] at F
    exact before_arrival_no_front hp u b (f::z) D P J K F
  rcases List.append_eq_append_iff.mp (show pre++e::post=u++arrival::quiet from W.symm) with
    ⟨t,A,H⟩|⟨t,A,H⟩
  · cases t with
    | nil =>
      have eq : pre=u := by simpa using A.symm
      have F := sound _ hit.1
      rw [eq,BStarResetSchedule.run_append,BStarResetSchedule.run_append step x a [launch]] at F
      exact before_arrival_no_front hp u u [] (List.append_nil _).symm P J K F
    | cons f t => exact M pre f t A hit.1

  · cases t with
    | nil =>
      have eq : pre=u := by simpa using A
      have no : ¬live ((a++[launch])++pre) := by
        intro H
        have F := sound _ H
        rw [eq,BStarResetSchedule.run_append,BStarResetSchedule.run_append step x a [launch]] at F
        exact before_arrival_no_front hp u u [] (List.append_nil _).symm P J K F
      exact no hit.1
    | cons f t =>
      have E := List.cons.inj H
      have fmem : e∈quiet := by rw [E.2]; exact List.mem_append_right _ List.mem_cons_self
      obtain ⟨s,S⟩ := hit.2
      exact offsite e fmem s S

#print axioms before_arrival_no_front
#print axioms credit_through_arrival
end L4.BStarAdmissionCreditFlight
