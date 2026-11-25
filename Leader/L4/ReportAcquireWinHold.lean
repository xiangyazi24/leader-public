import Leader.L4.ReportAcquireAllWins
import Leader.L4.ReportACQSelectedCapture

namespace L4.ReportAcquireWinHold
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportByteRows ReportOwnerAcquireProvenance
open ReportACQSelectedCapture ReportAcquireAllWins ReportGenerationAncestry
open ReportLeaseGrants ReportReaderRailNoRelease

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem acq_mark_holds_grant (d : Sheet) (C : Chart h)
    (N : 1<n) (x0 : Raw s n) (w : List (Fin n))
    (A : FlightAt d C x0 w) (e : Fin n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (rawRun x0 w i))=h i)
    (i : Nat) (I : i<C.L) (H : h (out C i)=true)
    (Compat : Compatible (rawGrant d (rawRun x0 w) (out C i)))
    (Held : rawGrant d (rawRun x0 w) (out C i) (C.route.port i)=true) :
    rawGrant d (rawNext s (rawRun x0 w) e) (out C i) (C.route.port i)=true := by
  let x := rawRun x0 w
  obtain ⟨g,R,O⟩ := flight_rail d C x0 w A
  have P : (readPC d C x).2≠0 := by
    rw [rail_opcode d C x g R,O]
    unfold acqOp
    omega
  have NR := positive_rail_no_release d C x g R P i I H
  have Canon : (oldIncidence d x (out C i)).canonical (C.route.port i)=true :=
    (canonical_eq (oldIncidence d x (out C i)) Compat _).trans Held
  apply (held_grant_survives_iff d x e (out C i) (C.route.port i)
    N ((mask _).trans H) Held).mpr
  unfold grantSurvives
  split
  · exact ⟨Canon,NR⟩
  · split
    · exact Canon
    · trivial

theorem compatible_run (d : Sheet) (N : 1<n) (x : Raw s n)
    (a : Fin n) (C : Compatible (rawGrant d x a)) (w : List (Fin n)) :
    Compatible (rawGrant d (rawRun x w) a) := by
  induction w generalizing x with
  | nil => exact C
  | cons e w IH =>
    exact IH _ (raw_compatible_step d x e a (edge_sep N e) C)

theorem acq_grant_from_prefix (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (i : Nat) (I : i<C.L) (H : h (out C i)=true)
    (Compat : Compatible (rawGrant d x0 (out C i)))
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (u : List (Fin n)) (P : u <+: w)
    (Held : rawGrant d (rawRun x0 u) (out C i) (C.route.port i)=true) :
    rawGrant d (rawRun x0 w) (out C i) (C.route.port i)=true := by
  induction T generalizing u with
  | nil =>
    have E := P.eq_of_length_le (Nat.zero_le _)
    subst u
    exact Held
  | @snoc ws e prev nc IH =>
    by_cases L : u.length≤ws.length
    · have Prefix := List.prefix_of_prefix_length_le P (List.prefix_append ws [e]) L
      have Held0 := IH u Prefix Held
      obtain ⟨Y,S⟩ := flight_run d C hh G F N x0 X A digit ws prev
      rw [ShortOwnerEpochJS.raw_snoc]
      exact acq_mark_holds_grant d C N x0 ws S e
        ((cached_fibre d N hh Q F).mask _ Y) i I H
        (compatible_run d N x0 (out C i) Compat ws) Held0
    · have E := P.eq_of_length_le (by simp; omega)
      subst u
      exact Held

/-- On a compatible first-cover fibre, all actually won old header
grants are still held at the real successful return and its consume.
No claim is made that a later reset/commit preserves this lease. -/
theorem successful_acq_grants_through_consume (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (Tag : (tok d C (rawRun x0 w) 0).tag=3)
    (ND : (tok d C (rawRun x0 w) 0).outcome≠1)
    (i : Nat) (I : i<C.L) (H : h (out C i)=true)
    (Compat : Compatible (rawGrant d x0 (out C i))) :
    rawGrant d (rawRun x0 w) (out C i) (C.route.port i)=true ∧
    rawGrant d (rawNext s (rawRun x0 w) (door C)) (out C i) (C.route.port i)=true := by
  let a := out C i
  obtain ⟨u,v,q,S,_,_,Held⟩ :=
    successful_root_all_wins d C hh G F N x0 X A digit w T Tag ND i I H
  have P : (u++[a]) <+: w := by
    rw [S]
    simp [a]
  have H0 : rawGrant d (rawRun x0 (u++[a])) a (C.route.port i)=true := by
    rw [ShortOwnerEpochJS.raw_snoc]
    exact Held
  have B := acq_grant_from_prefix d C hh G F N x0 X A digit i I H Compat w T
    (u++[a]) P H0
  obtain ⟨Y,M⟩ := flight_run d C hh G F N x0 X A digit w T
  exact ⟨B,acq_mark_holds_grant d C N x0 w M (door C)
    ((cached_fibre d N hh Q F).mask _ Y) i I H
    (compatible_run d N x0 a Compat w) B⟩

#print axioms acq_mark_holds_grant
#print axioms compatible_run
#print axioms acq_grant_from_prefix
#print axioms successful_acq_grants_through_consume
end L4.ReportAcquireWinHold
