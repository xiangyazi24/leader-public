import Leader.L4.ReportFastLeaseSupport
import Leader.L4.ReportFastFiveGeometry
import Leader.L4.ReportAcquireAllWins
import Leader.L4.ReportFastGateRaw

namespace L4.ReportFastTargetFence
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerCommandRail BStarShort
open ReportOwnerProvenanceTransport ReportFastGateRaw
open ReportByteRows ReportLeaseGrants ReportJoinedGrants ReportFastLeaseSupport

variable {s n : Nat} {h : Fin n → Bool}

/-- Old false lane survives every mark provided its own old outgoing
ACQ ASK is excluded when that outgoing mark is selected. -/
theorem absent_step (d : Sheet) (x : Raw s n) (N : 1<n) (e i : Fin n) (j : Fin 3)
    (A : rawGrant d x i j=false)
    (F : e=i → (oldView (params d s) (lower d (oldHeaders (rows s) (x i)))
      (selectBytes d (x i))).ask j=false) :
    rawGrant d (rawNext s x e) i j=false := by
  by_cases E : i=e
  · subst i
    exact no_ask_raw d x e N j A (F rfl)
  · by_cases R : i=rightNeighbor e
    · subst i
      exact incoming_no_create_raw d x e N j A
    · unfold rawGrant
      rw [ReportRawProjection.raw_spectator x e i E R]
      exact A

theorem acq_excludes_same_lane_release (p : Params) (u : BitVec p.w) (j : Fin 3)
    (A : grantAsk p true u (acqOp p) j=true) :
    grantAsk p true u 0 j=false := by
  by_cases R : grantAsk p true u 0 j=true
  · simp only [grantAsk,Bool.and_eq_true,beq_iff_eq] at A R
    have E : acqOp p=0 := A.2.symm.trans R.2
    unfold acqOp at E
    omega
  · exact Bool.eq_false_iff.mpr R

/-- Sufficient literal old-byte condition for the actual ACQ packet win,
not merely for a true post-mark grant bit. In particular a side ASK
requires the competing center ASK to be absent on this same mark. -/
theorem actual_free_win (d : Sheet) (x : Raw s n) (e : Fin n) (j : Fin 3)
    (Free : ∀ k,rawGrant d x e k=false)
    (Ask : grantAsk (params d s) true (selectBytes d (x e)) (acqOp (params d s)) j=true)
    (NoCentre : j≠1 → grantAsk (params d s) true (selectBytes d (x e))
      (acqOp (params d s)) 1=false) :
    acqFlightWin (params d s) true (selectBytes d (x e)) j=true := by
  change winOld (params d s) (selectBytes d (x e))
    (grantAsk (params d s) true (selectBytes d (x e)) (acqOp (params d s)))
    (grantAsk (params d s) true (selectBytes d (x e)) 0) j=true
  exact old_grant_free_wins _ _ _ _ j Free Ask (acq_excludes_same_lane_release _ _ _ Ask) NoCentre

/-- No new rival grant on the actual sampled prefix, using only old outgoing
ASK exclusion. Incoming and spectator marks need no steering hypothesis. -/
def NoAskOnTape (d : Sheet) (i : Fin n) (j : Fin 3) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w => (e=i → (oldView (params d s) (lower d (oldHeaders (rows s) (x i)))
      (selectBytes d (x i))).ask j=false) ∧
    NoAskOnTape d i j (rawNext s x e) w

theorem absent_run (d : Sheet) (N : 1<n) (i : Fin n) (j : Fin 3)
    (x : Raw s n) (w : List (Fin n))
    (A : rawGrant d x i j=false) (F : NoAskOnTape d i j x w) :
    rawGrant d (rawRun x w) i j=false := by
  induction w generalizing x with
  | nil => exact A
  | cons e w IH =>
    exact IH _ (absent_step d x N e i j A F.1) F.2

/-- A fence on the literal prefix ending at one of the three header visits
is enough to produce that visit's actual ACQ win. -/
theorem actual_visit_win (d : Sheet) (N : 1<n) (x : Raw s n)
    (w : List (Fin n)) (i : Fin n) (j : Fin 3)
    (A : ∀ k,rawGrant d x i k=false) (F : ∀ k,NoAskOnTape d i k x w)
    (Ask : grantAsk (params d s) true (selectBytes d (rawRun x w i))
      (acqOp (params d s)) j=true)
    (NoCentre : j≠1 → grantAsk (params d s) true (selectBytes d (rawRun x w i))
      (acqOp (params d s)) 1=false) :
    acqFlightWin (params d s) true (selectBytes d (rawRun x w i)) j=true :=
  actual_free_win d (rawRun x w) i j
    (fun k => absent_run d N i k x w (A k) (F k)) Ask NoCentre

/-- An old report ASK is a healthy ACQ front at the owned occurrence. -/
theorem ask_shape (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat)
    (Mask : lower d (oldHeaders (rows s) (x (out C k)))=h (out C k))
    (A : (oldView (params d s) (lower d (oldHeaders (rows s) (x (out C k))))
      (selectBytes d (x (out C k)))).ask (C.route.port k)=true) :
    (tok d C x k).tag=2 ∧ (tok d C x k).fault=false ∧
      (tok d C x k).opcode=acqOp (params d s) := by
  rw [Mask] at A
  rw [predecessor_projection]
  change (_ && _ && _) = true at A
  simp only [Bool.and_eq_true,beq_iff_eq] at A
  refine ⟨A.1.1,?_,A.2⟩
  have B := A.1.2
  change (!_)=true at B
  simp at B
  exact B

theorem no_ask_of_non_acq_token (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat)
    (Mask : lower d (oldHeaders (rows s) (x (out C k)))=h (out C k))
    (NoOp : (tok d C x k).opcode≠acqOp (params d s)) :
    (oldView (params d s) (lower d (oldHeaders (rows s) (x (out C k))))
      (selectBytes d (x (out C k)))).ask (C.route.port k)=false :=
  Bool.eq_false_iff.mpr (fun A=>NoOp (ask_shape d C x k Mask A).2.2)

/-- StrongSerial makes lack of an ACQ PC sufficient for the entire
chart to place no old outgoing ASK, including on a fault-normalized front. -/
theorem no_ask_of_non_acq_pc (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat)
    (K : k<C.L) (S : StrongSerial d C x)
    (Mask : lower d (oldHeaders (rows s) (x (out C k)))=h (out C k))
    (NoOp : (readPC d C x).2≠acqOp (params d s)) :
    (oldView (params d s) (lower d (oldHeaders (rows s) (x (out C k))))
      (selectBytes d (x (out C k)))).ask (C.route.port k)=false := by
  apply Bool.eq_false_iff.mpr
  intro A
  obtain ⟨Tag,Live,Op⟩ := ask_shape d C x k Mask A
  exact NoOp ((S.2 k K (.inl Tag) Live).symm.trans Op)

/-- Divergence from the win route is numerical, not just a ghost bit:
the old ready race4 actually puts payload zero on the outgoing F. -/
theorem deny_departure_payload (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) {Q : Raw s n → Prop} (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i+1<C.L)
    (A : chartGate d C x i=true) (B : chartGate d C x (i+1)=false)
    (H : healthyAdmit (params d s) (tok d C x i))
    (R : (tok d C x i).race=4) :
    (tok d C (rawNext s x (out C i)) (i+1)).payload=0 := by
  have E := (raw_ready_depart d C N hh G F x X i I A B H (by omega)).2
  rw [E]
  simp [R]

/-- A healthy denied ADMIT return takes the literal retry-to-ISSUE0 branch. -/
theorem deny_consume_issue0 (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (P : readPC d C x=(2,admitOp (params d s)))
    (T : (tok d C x 0).tag=3) (O : (tok d C x 0).opcode=admitOp (params d s))
    (F0 : (tok d C x 0).fault=false) (Q0 : (tok d C x 0).outcome=0)
    (Denied : (tok d C x 0).payload=0) :
    readPC d C (rawNext s x (door C))=(1,0) := by
  simpa [Denied] using (raw_admit_consume d C N x mask P T O F0 Q0).1

/-- The only numerical ingress to ACQ from a different source command
is the ADMIT consume on the own incoming door. -/
theorem fresh_acq_requires_admit_door (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) {Q : Raw s n → Prop} (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (S : StrongSerial d C x) (e : Fin n)
    (H : (readPC d C x).2≠acqOp (params d s))
    (E : (readPC d C (rawNext s x e)).2=acqOp (params d s)) :
    e=door C ∧ (readPC d C x).2=admitOp (params d s) := by
  have Door : e=door C := by
    by_cases Z : e=door C
    · exact Z
    · have M := (cached_fibre d N hh Q F).mask x X
      have P := congrArg Prod.snd (ReportPrelaunchClock.raw_nondoor_control d C x e N M Z)
      exact False.elim (H (P.symm.trans E))
  refine ⟨Door,?_⟩
  rcases pc_step_with_phase d C N hh G F digit x X S e with R|R|⟨_,R⟩
  · have Z := R.1
    rw [E] at Z
    unfold acqOp at Z
    omega
  · exact False.elim (H (R.symm.trans E))
  · have hnext {t a b : Nat} (D : 0<t) (P : PreviewNextOp t a b)
        (B : b=t+2) : a=t+1 := by
      cases P <;> omega
    exact hnext digit R E

#print axioms fresh_acq_requires_admit_door
#print axioms absent_step
#print axioms actual_free_win
#print axioms actual_visit_win
#print axioms no_ask_of_non_acq_pc
#print axioms deny_departure_payload
#print axioms deny_consume_issue0
end L4.ReportFastTargetFence
