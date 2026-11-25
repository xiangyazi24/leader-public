import Leader.L4.ReportFastOwnerSupport
import Leader.L4.ReportRootLeaseBoundary
import Leader.L4.ReportIndexedSourcePrefix

namespace L4.ReportFastLeaseSupport
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerProvenanceTransport
open ReportOwnerCommandRail ReportOwnerSerial ReportPrelaunchAllOwners
open ReportGoodEightBank ReportGoodEightCut ReportFastOwnerSupport
open ReportGateGeometry ReportAdaptiveFibre
open ReportByteRows ReportJoinedGrants ReportLeaseGrants ReportLeaseOwner
open ReportPrelaunchClock ReportOwnerAcquireReturn ReportRootLeaseBoundary
open ReportIndexedSourcePrefix

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

private theorem fast_free_grant_next (p : Params) (u : BitVec p.w) (j : Fin 3)
    (Free : ∀ k,u.getLsbD (grantAddr p k)=false)
    (Ask : grantAsk p true u (acqOp p) j=true)
    (NoRel : grantAsk p true u 0 j=false)
    (Rival : j≠1→grantAsk p true u (acqOp p) 1=false) :
    grantNext p true u j=true := by
  have W := old_grant_free_wins p u
    (grantAsk p true u (acqOp p)) (grantAsk p true u 0) j Free Ask NoRel Rival
  simp [grantNext,W]

theorem service_joined_grants (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (j : Fin 3) :
    let p := params d s
    let v := rightNeighbor e
    let hu := lower d (oldHeaders (rows s) (x e))
    let hv := lower d (oldHeaders (rows s) (x v))
    rawGrant d (rawNext s x e) e j=(oldView p hu (selectBytes d (x e))).nextValue j ∧
    rawGrant d (rawNext s x e) v j=(if hv then
      (oldView p hv (selectBytes d (x v))).canonical j else false) :=
  raw_grant_rows d x e (edge_sep N e) j

theorem no_ask_raw (d : Sheet) (x : Raw s n) (e : Fin n) (N : 1<n)
    (j : Fin 3)
    (O : rawGrant d x e j=false)
    (A : (oldView (params d s) (lower d (oldHeaders (rows s) (x e)))
      (selectBytes d (x e))).ask j=false) :
    rawGrant d (rawNext s x e) e j=false := by
  rw [(service_joined_grants d x e N j).1]
  exact no_ask_no_create _ j O A

theorem release_raw (d : Sheet) (x : Raw s n) (e : Fin n) (N : 1<n)
    (j : Fin 3)
    (R : (oldView (params d s) (lower d (oldHeaders (rows s) (x e)))
      (selectBytes d (x e))).release j=true) :
    rawGrant d (rawNext s x e) e j=false := by
  rw [(service_joined_grants d x e N j).1]
  exact release_next_false _ j R

theorem incoming_no_create_raw (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (j : Fin 3) (O : rawGrant d x (rightNeighbor e) j=false) :
    rawGrant d (rawNext s x e) (rightNeighbor e) j=false := by
  have W := raw_grant_rows d x e (edge_sep N e) j
  have R := received_no_create (params d s)
    (lower d (oldHeaders (rows s) (x (rightNeighbor e))))
    (selectBytes d (x (rightNeighbor e))) j O
  -- CHECK: grantReceived is definitionally the responder value
  -- in ReportLeaseGrants.raw_grant_rows:97–116.
  exact W.2.trans R

-- Old-free win, with actual raw next assignment.  The hypotheses
-- explicitly include the competing center ASK, not just old grants.
theorem free_win_raw (d : Sheet) (x : Raw s n) (e : Fin n) (N : 1<n)
    (H : lower d (oldHeaders (rows s) (x e))=true) (j : Fin 3)
    (Free : ∀ k,rawGrant d x e k=false)
    (Ask : grantAsk (params d s) true (selectBytes d (x e))
       (acqOp (params d s)) j=true)
    (NoRel : grantAsk (params d s) true (selectBytes d (x e)) 0 j=false)
    (Rival : j≠1 → grantAsk (params d s) true (selectBytes d (x e))
       (acqOp (params d s)) 1=false) :
    rawGrant d (rawNext s x e) e j=true := by
  let p := params d s
  let u := selectBytes d (x e)
  have A := (service_joined_grants d x e N j).1
  rw [H,next_agrees] at A
  exact A.trans (fast_free_grant_next (params d s) (selectBytes d (x e)) j
    Free Ask NoRel Rival)

-- Every already-held incidence on a positive serial rail survives
-- even an abort initiation at the owner door. RESET departure is
-- the later release event, not the door's change to ISSUE0.
theorem held_from_bank (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (B : GoodEightBank d hh Q G x)
    (C : Chart h) (M : C∈ownerCharts G)
    (P : (readPC d C x).2≠0) (e : Fin n) (k : Nat) (K : k<C.L)
    (Hdr : h (out C k)=true)
    (Held : rawGrant d x (out C k) (C.route.port k)=true) :
    rawGrant d (rawNext s x e) (out C k) (C.route.port k)=true := by
  have X : Cached d hh Q x := B.2.1.1.1.1
  have Compat := B.2.1.1.2 (out C k) Hdr
  exact held_incidence_step d C N x e ((cached_fibre d N hh Q F).mask x X)
    (serial_from_bank d N hh G F digit x B C M) P k K Hdr Compat Held

-- The post-ACQ source-order implication is now a genuine theorem.
-- RootHeldThrough concerns the same word w, not existential fresh history.
theorem ordered_acks_from_held_root (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (A : StrongSerial d C x)
    (PC : PostAcqPC (params d s) (readPC d C x))
    (w : List (Fin n)) (Held : RootHeldThrough d C x w)
    (End : (readPC d C (rawRun x w)).2≠0) :
    ∃ l, AckTape d C x w l ∧
      logicalPC d C (rawRun x w)=logicalPC d C x+l.length ∧
      OrderedFrom (params d s) (logicalPC d C x) l := by
  have Pos : (readPC d C x).2≠0 := by
    have K := PC.2.1
    unfold cmpOp at K
    omega
  have NR := no_restart_of_held_endpoint d C N hh G F digit x X A Pos w Held End
  obtain ⟨l,T⟩ := ack_tape_run d C N hh G F digit x X A PC w NR
  exact ⟨l,T,tape_count d C x w l T,tape_order d C x w l T⟩

end L4.ReportFastLeaseSupport

