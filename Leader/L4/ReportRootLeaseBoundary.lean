import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportAcquireWinHold

namespace L4.ReportRootLeaseBoundary
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportLeaseGrants
open ReportGenerationAncestry ReportOwnerCommandRail
open ReportOwnerAcquireProvenance ReportAcquireWinHold ReportLeaseOwner
open ReportOwnerIssueControl

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- The release of the original lane-0 grant is on the actual old
outgoing RESET0 mark. It is neither source retry nor a later reply. -/
def RootRelease (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  e=C.root ∧ (oldIncidence d x C.root).release 0=true

def NoRootReleaseTape (d : Sheet) (C : Chart h) :
    Raw s n→List (Fin n)→Prop
  | _,[]=>True
  | x,e::w=>¬RootRelease d C x e ∧ NoRootReleaseTape d C (rawNext s x e) w

theorem root_grant_step_iff (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (e : Fin n)
    (Hdr : lower d (oldHeaders (rows s) (x C.root))=true)
    (Compat : Compatible (rawGrant d x C.root))
    (Held : rawGrant d x C.root 0=true) :
    rawGrant d (rawNext s x e) C.root 0=true ↔ ¬RootRelease d C x e := by
  have Canon := (canonical_eq (oldIncidence d x C.root) Compat 0).trans Held
  rw [held_grant_survives_iff d x e C.root 0 N Hdr Held]
  unfold grantSurvives RootRelease
  by_cases E : C.root=e
  · rw [if_pos E,Canon]
    constructor
    · rintro ⟨_,F⟩ ⟨_,R⟩
      rw [F] at R
      contradiction
    · intro H
      refine ⟨rfl, Bool.eq_false_iff.mpr ?_⟩
      intro R
      exact H ⟨E.symm,R⟩
  · rw [if_neg E]
    by_cases R : C.root=rightNeighbor e
    · rw [if_pos R,Canon]
      exact ⟨fun _ H=>E H.1.symm,fun _=>rfl⟩
    · rw [if_neg R]
      exact ⟨fun _ H=>E H.1.symm,fun _=>trivial⟩

private theorem held_head (d : Sheet) (C : Chart h)
    (x : Raw s n) (w : List (Fin n)) (H : RootHeldThrough d C x w) :
    rawGrant d x C.root 0=true := by
  have U : out C 0=C.root := rfl
  have V : C.route.port 0=0 := C.rootPort
  cases w with
  | nil =>
    change rawGrant d x (out C 0) (C.route.port 0)=true at H
    rwa [U,V] at H
  | cons e w =>
    have A := H.1
    change rawGrant d x (out C 0) (C.route.port 0)=true at A
    rwa [U,V] at A

/-- Exact trace bridge. On a compatible frozen fibre the original
grant is held through the whole word iff no actual old release
mark occurs. In particular this is not a condition on PC values. -/
theorem root_held_iff_no_release (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (Compat : Compatible (rawGrant d x C.root))
    (Held : rawGrant d x C.root 0=true) (w : List (Fin n)) :
    RootHeldThrough d C x w ↔ NoRootReleaseTape d C x w := by
  let CF := cached_fibre d N hh Q F
  have U : out C 0=C.root := rfl
  have V : C.route.port 0=0 := C.rootPort
  induction w generalizing x with
  | nil =>
    constructor
    · intro _
      trivial
    · intro _
      change rawGrant d x (out C 0) (C.route.port 0)=true
      rwa [U,V]
  | cons e w IH =>
    let y := rawNext s x e
    have A : rawGrant d y C.root 0=true ↔ ¬RootRelease d C x e :=
      root_grant_step_iff d C N x e ((CF.mask x X C.root).trans C.rootHeader) Compat Held
    have C' := raw_compatible_step d x e C.root (edge_sep N e) Compat
    have Y := CF.closed x e X
    constructor
    · intro H
      have T := H.2
      have B := held_head d C y w T
      exact ⟨A.mp B,(IH y Y C' B).mp T⟩
    · rintro ⟨H,T⟩
      have B := A.mpr H
      refine ⟨?_,(IH y Y C' B).mpr T⟩
      change rawGrant d x (out C 0) (C.route.port 0)=true
      rwa [U,V]

/-- The original root grant comes from the actual lane-0 ACQ win
and survives the consume. A no-release generation prefix, on that
same suffix, needs no separate continuous-grant witness. -/
theorem root_held_after_success_before_release (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (P : readPC d C x=(1,acqOp (params d s)))
    (Compat : Compatible (rawGrant d x C.root)) (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s x (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s x (door C)) w) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s x (door C)) w) 0).outcome≠1)
    (v : List (Fin n)) :
    let after := rawNext s (rawRun (rawNext s x (door C)) w) (door C)
    NoRootReleaseTape d C after v → RootHeldThrough d C after v := by
  dsimp only
  let x0 := rawNext s x (door C)
  let y := rawRun x0 w
  let after := rawNext s y (door C)
  obtain ⟨X0,A⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N x X I P
  obtain ⟨Y,_⟩ := flight_run d C hh G F N x0 X0 A digit w T
  have C0 : Compatible (rawGrant d x0 C.root) :=
    raw_compatible_step d x (door C) C.root (edge_sep N _) Compat
  have U : out C 0=C.root := rfl
  have V : C.route.port 0=0 := C.rootPort
  have C0' : Compatible (rawGrant d x0 (out C 0)) := by rwa [U]
  have H := (successful_acq_grants_through_consume d C hh G F N x0 X0 A digit w T Tag ND
    0 C.positive C.rootHeader C0').2
  have B : rawGrant d after C.root 0=true := by
    rw [U,V] at H
    exact H
  have C1 : Compatible (rawGrant d after C.root) :=
    raw_compatible_step d y (door C) C.root (edge_sep N _)
      (compatible_run d N x0 C.root C0 w)
  exact (root_held_iff_no_release d C N hh F after
    ((cached_fibre d N hh Q F).closed y (door C) Y) C1 B v).mpr

#print axioms root_grant_step_iff
#print axioms root_held_iff_no_release
#print axioms root_held_after_success_before_release
/-- Authenticate the actual captured bit at the current pre-SEAL
endpoint without assuming either NoRestartTape or OwnerRailTape.
The sampled suffix ends before the actual old root RESET release.
No continuous-grant hypothesis is required. -/
theorem authentic_capture_current_no_root_release (d : Sheet) (G : GapInput h) (r : Owner h)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (Compat : Compatible (rawGrant d x (charter G r).root))
    (I : LegalIssue d (charter G r) x)
    (P : readPC d (charter G r) x=(1,acqOp (params d s))) (digit : 0<(params d s).digits)
    (w : List (Fin n))
    (T : ReportOwnerAcquireProvenance.BeforeConsume d (charter G r)
      (rawNext s x (door (charter G r))) w)
    (Tag : (tok d (charter G r) (rawRun (rawNext s x (door (charter G r))) w) 0).tag=3)
    (ND : (tok d (charter G r) (rawRun (rawNext s x (door (charter G r))) w) 0).outcome≠1)
    (v : List (Fin n))
    (NoRelease : NoRootReleaseTape d (charter G r)
      (rawNext s (rawRun (rawNext s x (door (charter G r))) w) (door (charter G r))) v)
    (Lo : cmpOp (params d s)≤(readPC d (charter G r)
      (rawRun (rawNext s (rawRun (rawNext s x (door (charter G r))) w)
        (door (charter G r))) v)).2)
    (Hi : (readPC d (charter G r)
      (rawRun (rawNext s (rawRun (rawNext s x (door (charter G r))) w)
        (door (charter G r))) v)).2<sealOp (params d s)) :
    let C := charter G r
    let z := rawRun (rawNext s (rawRun (rawNext s x (door C)) w) (door C)) v
    ReportWriterPayload.capturedSelector (params d s) (selectBytes d (z C.root))=
      rawSelector d z (centre C) := by
  have Held := root_held_after_success_before_release d (charter G r) hh G F N
    x X I P Compat digit w T Tag ND v NoRelease
  exact authentic_capture_current_while_held d G r hh F N x X I P digit w T Tag ND v Held Lo Hi

#print axioms authentic_capture_current_no_root_release
end L4.ReportRootLeaseBoundary
