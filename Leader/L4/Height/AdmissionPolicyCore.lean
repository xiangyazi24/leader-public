import Leader.L4.Height.AdmissionCreditBridge
import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarFenceReceiverChart
import Leader.L4.Height.ServiceCustody
import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarSteeredLikelihood

namespace L4.Height.AdmissionPolicyCore
open PhysicalCustody BStarSteeredLikelihood
variable {s n : Nat}
local notation "hp" => (show 0<2 by decide)

open BStarClearanceSource

/-- The last own launch on the emitted prefix issued ADMIT after the query.
All intervening old door rows are tested for a physical launch. -/
def newAdmission (origin : Raw s n) (root : Fin n) (a : Word n) : Prop :=
  ∃ u e v, a=u++e::v ∧ BStarAdmissionCreditFlight.genuineIssue hp origin root u e ∧
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

open AllSizeProtocol BStarAcquireLiteralChain BStarH6WordChart BStarAcquireAnchors
open BStarH6Ordinal BStarClearanceRaceMark BStarFenceReceiverChart BStarLongClaims BStarParkedSteering
noncomputable section
def client {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true) (o : Owners h) (j : Fin 5) : Owners h :=
  let M : Int := total h
  let q := (o.val+j.val-2)%M
  have pos : 0<M := by have H := total_pos h hh; dsimp [M]; omega
  ⟨q,Int.emod_nonneg _ (Int.ne_of_gt pos),Int.emod_lt_of_pos _ pos⟩

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base

def serviceOwner (i : Header h) : Owners h := ⟨commandOwner h i.val 1,commandOwner_range h g.hh i.val 1⟩

theorem service_header (i : Header h) : (endpoint h g.hh (serviceOwner g i) 1).1=i.val :=
  congrArg Prod.fst ((endpoint_spec h g.hh (serviceOwner g i) 1).2.2 i.val i.property rfl).symm

def gate (o : Owners h) (j : Fin 5) : Fin n :=
  digitFrom (endpoint h g.hh (client h g.hh o j) 1).1 2

theorem gate_address (large : 6 ≤ s) (o : Owners h) (j : Fin 5) :
    BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh (gate g o j)=2 ∧
    commandOwner h (gate g o j) 1=(client h g.hh o j).val := by
  have ep := endpoint_spec h g.hh (client h g.hh o j) 1
  have two : 2<radWidth s := by
    have z := Nat.pow_le_pow_right (n:=2) (by decide) large
    unfold radWidth
    change 64≤2^s at z
    omega
  obtain ⟨ord,wordAt⟩ := digit_from hp ep.1 (radWidth s) g.notShort 2 two
  refine ⟨ord,?_⟩
  exact (congrArg (fun q => BStarLongFiberOwner.owner (↑(total h)) q
    (BStarLongFiberOwner.cmdDispl 1)) wordAt).trans ep.2.1

def issue (o : Owners h) (j : Fin 5) :=
  BStarAdmissionCreditFlight.genuineIssue hp x (endpoint h g.hh (client h g.hh o j) 0).1

def redirect (o : Owners h) (live : Fin 5 → Word n → Prop) :=
  AdmissionMask.mask h g.hh (gate g o) (issue g o) live
    (fun _ i => if commandOwner h i 1=o.val then .left else .right)

def live (o : Owners h) (phase : Fin 5 → Word n → Prop) (j : Fin 5) (a : Word n) : Prop :=
  (phase j a ∧ ¬RawServiceCore.publishes x (endpoint (oldH6 (rows s) g.base) g.hh o 1).1 a) ∧
    newAdmission x
    (endpoint (oldH6 (rows s) g.base) g.hh (client _ g.hh o j) 0).1 a ∧
    firstAdmission hp (base:=g.base) (hh:=g.hh) (rawRun x a) (gate g o j)

theorem live_gate (o : Owners h) (phase : Fin 5→Word n→Prop) (j : Fin 5) (a : Word n)
    (L : live g o phase j a) :
    firstAdmission hp (base:=g.base) (hh:=g.hh) (rawRun x a) (gate g o j) :=
  L.2.2

theorem selected_live (o : Owners h) (large : 6≤s) (phase : Fin 5→Word n→Prop)
    (j : Fin 5) (b : Word n) (side : Side) (L : live g o phase j b)
    (A : AdmissionMask.credit (issue g o j) (AdmissionMask.hitAt (gate g o j)
      (live g o phase j)) b=true) :
    chooseBy (redirect g o (live g o phase)) b (incident (gate g o j) side)=
      incident (gate g o j) (if (client h g.hh o j).val=o.val then .left else .right) := by
  obtain ⟨ord,owner⟩ := gate_address g large o j
  have hit := AdmissionCreditBridge.selected h g.hh (gate g o) (issue g o)
    (live g o phase) (fun _ i => if commandOwner h i 1=o.val then .left else .right) b j side ord L A
  simpa only [redirect, owner] using hit

/-- Physical flight, old emitted quiet gap, then either candidate incidence,
all on one literal tape. The actual arrival must establish the concrete live
predicate; the theorem does not infer arrival from a scheduled label alone. -/
theorem selected_after_flight (o : Owners h) (large : 6≤s)
    (phase : Fin 5→Word n→Prop) (j : Fin 5) (a u quiet : Word n)
    (launch arrival : Fin n) (side : Side)
    {addr : Nat→Pos n} {len k d : Nat}
    (rootAt : (addr 0).1=(endpoint h g.hh (client h g.hh o j) 0).1)
    (K1 : addr k=(gate g o j,1))
    (I : issue g o j a launch)
    (P : BusyOnly hp g.base addr len admit (rawNext s (rawRun x a) launch) (.out 0) u (.out d))
    (D : d<k) (K : k≤len)
    (offsite : ∀ e∈quiet,∀ s,e≠incident (gate g o j) s)
    (eligible : live g o phase j ((a++[launch])++(u++arrival::quiet))) :
    let b := (a++[launch])++(u++arrival::quiet)
    chooseBy (redirect g o (live g o phase)) b (incident (gate g o j) side)=
      incident (gate g o j) (if (client h g.hh o j).val=o.val then .left else .right) := by
  dsimp only
  apply selected_live g o large phase j _ side eligible
  have I' : BStarAdmissionCreditFlight.genuineIssue hp x (addr 0).1 a launch := by
    rw [rootAt]; exact I
  have A := AdmissionCreditBridge.armed hp (hh:=g.hh) a u quiet launch arrival
    (gate g o j) K1 I' P D K (live g o phase j) (live_gate g o phase j) offsite
  rw [rootAt] at A
  exact A

end
end L4.Height.AdmissionPolicyCore
