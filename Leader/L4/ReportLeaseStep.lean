import Leader.L4.ReportPrelaunchAllOwners

namespace L4.ReportLeaseStep
open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ReportByteRows ReportRawProjection ReportOwnerResetDrain
open ShortResetCycle ShortResetChart ReportResetBarrier
open ReportPrelaunchK1Geometry

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

variable {s n : Nat} {h : Fin n→Bool}

-- BStarShort.lean:25–53. An already-set bit never wins again.
theorem held_no_win (g : BStarShort.GrantView) (j : Fin 3)
    (O : g.old j=true) : g.win j=false := by
  by_cases J : j=1
  · subst j
    simp [BStarShort.GrantView.win,BStarShort.GrantView.centerWin,
      BStarShort.GrantView.canonical,O]
  · cases K : g.old 1 <;>
      simp [BStarShort.GrantView.win,BStarShort.GrantView.canonical,J,K,O]

theorem held_next_iff (g : BStarShort.GrantView) (j : Fin 3)
    (H : g.header=true) (O : g.old j=true) :
    g.nextValue j=true ↔ g.canonical j=true ∧ g.release j=false := by
  simp [BStarShort.GrantView.nextValue,H,held_no_win g j O]

-- The next two projections duplicate checked PRIVATE helpers, so this
-- module does not depend on their visibility.
-- CHECK: ReportOwnerResetDrain.lean:460–482.
theorem raw_grant_pair (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (j : Fin 3)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i) :
    grantBit sheet (rawNext s x e) e j=
        grantNext (params sheet s) (h e) (selectBytes sheet (x e)) j ∧
    grantBit sheet (rawNext s x e) (rightNeighbor e) j=
        grantReceived (params sheet s) (h (rightNeighbor e))
          (selectBytes sheet (x (rightNeighbor e))) j := by
  cases sheet with
  | first =>
    have A := ReportJoinedGrants.service_joined_grants_report1
      x e (edge_sep N e) j
    dsimp only at A
    rw [← mask e, ← mask (rightNeighbor e)]
    exact A
  | second =>
    have A := ReportJoinedGrants.service_joined_grants_report2
      x e (edge_sep N e) j
    dsimp only at A
    rw [← mask e, ← mask (rightNeighbor e)]
    exact A

-- CHECK: ReportOwnerResetDrain.lean:900–937.
theorem raw_pair_bytes (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i) :
    (selectBytes sheet (rawNext s x e e),
      selectBytes sheet (rawNext s x e (rightNeighbor e))) =
      join (params sheet s) (h e,h (rightNeighbor e))
        (selectBytes sheet (x e),selectBytes sheet (x (rightNeighbor e))) := by
  cases sheet with
  | first =>
    have R := raw_report1_pair x e (edge_sep N e)
    dsimp only at R
    rw [← mask e, ← mask (rightNeighbor e)]
    exact R
  | second =>
    have R := raw_report2_pair x e (edge_sep N e)
    dsimp only at R
    rw [← mask e, ← mask (rightNeighbor e)]
    exact R

theorem raw_low_pair (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i<grantBase (params sheet s)) :
    let p := params sheet s
    let u := selectBytes sheet (x e)
    let v := selectBytes sheet (x (rightNeighbor e))
    let q := row p (h e,h (rightNeighbor e)) (u,v)
    (selectBytes sheet (rawNext s x e e)).getLsbD i=(q.1.apply u).getLsbD i ∧
    (selectBytes sheet (rawNext s x e (rightNeighbor e))).getLsbD i=
      (q.2.apply v).getLsbD i := by
  let p := params sheet s
  let u := selectBytes sheet (x e)
  let v := selectBytes sheet (x (rightNeighbor e))
  have P := raw_pair_bytes sheet x e N mask
  have J := join_work_bits p (h e,h (rightNeighbor e)) (u,v) i I
  exact ⟨(congrArg (fun z : Pair (BitVec p.w)=>z.1.getLsbD i) P).trans J.1,
    (congrArg (fun z : Pair (BitVec p.w)=>z.2.getLsbD i) P).trans J.2⟩

-- CHECK: ReportJoinedGrants.lean:7–19; oldView.old is definitionally
-- the same bit as grantBit, using BStarShort.grantView.
theorem initiator_held_iff (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (j : Fin 3)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : h e=true) (O : grantBit sheet x e j=true) :
    let g := ReportJoinedGrants.oldView (params sheet s) true
      (selectBytes sheet (x e))
    grantBit sheet (rawNext s x e) e j=true ↔
      g.canonical j=true ∧ g.release j=false := by
  dsimp only
  have A := (raw_grant_pair sheet x e N j mask).1
  rw [H,←ReportJoinedGrants.next_agrees] at A
  rw [A]
  exact held_next_iff _ j rfl O

-- No old-bit assumption needed for the responder projection.
theorem responder_held_iff (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (j : Fin 3)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : h (rightNeighbor e)=true) :
    let g := ReportJoinedGrants.oldView (params sheet s) true
      (selectBytes sheet (x (rightNeighbor e)))
    grantBit sheet (rawNext s x e) (rightNeighbor e) j=true ↔
      g.canonical j=true := by
  dsimp only
  have A := (raw_grant_pair sheet x e N j mask).2
  rw [H] at A
  rw [A]
  rfl

/-- Exact condition at a single physical grant incidence; not an
    assumption that the owner generation is authentic. -/
def HoldAt (sheet : Sheet) (x : Raw s n) (e q : Fin n) (j : Fin 3) : Prop :=
  let g := ReportJoinedGrants.oldView (params sheet s) true
    (selectBytes sheet (x q))
  (q=e → g.canonical j=true ∧ g.release j=false) ∧
  (q=rightNeighbor e → g.canonical j=true)

theorem held_step_iff (sheet : Sheet) (x : Raw s n) (e q : Fin n)
    (N : 1<n) (j : Fin 3)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : h q=true) (O : grantBit sheet x q j=true) :
    grantBit sheet (rawNext s x e) q j=true ↔ HoldAt sheet x e q j := by
  by_cases L : q=e
  · subst q
    have K := initiator_held_iff sheet x e N j mask H O
    simpa [HoldAt,edge_sep N e] using K
  · by_cases R : q=rightNeighbor e
    · subst q
      have K := responder_held_iff sheet x e N j mask H
      simpa [HoldAt,L] using K
    · have E : grantBit sheet (rawNext s x e) q j =
          grantBit sheet x q j := by
        unfold grantBit
        rw [raw_spectator x e q L R]
      simp [E,O,HoldAt,L,R]

/-- The cached-fibre version: no fresh scheduler or cached surrogate. -/
theorem cached_held_step_iff (sheet : Sheet) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q) (N : 1<n)
    (x : Raw s n) (X : Cached sheet hh Q x)
    (e q : Fin n) (j : Fin 3) (H : h q=true)
    (O : grantBit sheet x q j=true) :
    grantBit sheet (rawNext s x e) q j=true ↔ HoldAt sheet x e q j :=
  held_step_iff sheet x e q N j ((cached_fibre sheet N hh Q F).mask x X) H O

-- A corrected disjunction: Release is an externally established
-- SAME-GENERATION event (not merely the decoded old F0).
theorem grant_hold_or_release (sheet : Sheet) (x : Raw s n) (e q : Fin n)
    (N : 1<n) (j : Fin 3)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : h q=true) (O : grantBit sheet x q j=true)
    (Release : Prop)
    (C : (ReportJoinedGrants.oldView (params sheet s) true
      (selectBytes sheet (x q))).canonical j=true)
    (A : q=e → (ReportJoinedGrants.oldView (params sheet s) true
      (selectBytes sheet (x q))).release j=true → Release) :
    grantBit sheet (rawNext s x e) q j=true ∨ Release := by
  let g := ReportJoinedGrants.oldView (params sheet s) true
    (selectBytes sheet (x q))
  by_cases L : q=e
  · cases R : g.release j
    · apply Or.inl
      apply (held_step_iff sheet x e q N j mask H O).mpr
      exact ⟨fun _=>⟨C,R⟩,fun _=>C⟩
    · exact Or.inr (A L R)
  · apply Or.inl
    apply (held_step_iff sheet x e q N j mask H O).mpr
    exact ⟨fun K=>False.elim (L K),fun _=>C⟩

-- The genuine release is the outgoing old F0 mark, not the D0 receipt.
-- This also applies to an inherited F0 and demonstrates the need for
-- provenance in classifying A above.
theorem departing_reset_drops_grant (sheet : Sheet) (x : Raw s n)
    (e : Fin n) (N : 1<n) (j : Fin 3)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : h e=true)
    (T : publicationToken (params sheet s) true
      (selectBytes sheet (x e)) j=reset0Forward) :
    grantBit sheet (rawNext s x e) e j=false := by
  have R : (ReportJoinedGrants.oldView (params sheet s) true
      (selectBytes sheet (x e))).release j=true := by
    change ((publicationToken (params sheet s) true (selectBytes sheet (x e)) j).tag==2 &&
      !(publicationToken (params sheet s) true (selectBytes sheet (x e)) j).fault &&
      (publicationToken (params sheet s) true (selectBytes sheet (x e)) j).opcode==0)=true
    rw [T]
    rfl
  have E := (raw_grant_pair sheet x e N j mask).1
  rw [H,←ReportJoinedGrants.next_agrees] at E
  exact E.trans (ReportJoinedGrants.release_next_false _ _ R)

theorem departing_reset_clears_seal (sheet : Sheet) (x : Raw s n)
    (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : h e=true)
    (T : publicationToken (params sheet s) true
      (selectBytes sheet (x e)) 1=reset0Forward) :
    drainSealZero (params sheet s) (selectBytes sheet (rawNext s x e e)) := by
  let p := params sheet s
  have W := drain_row_seal_release p (h (rightNeighbor e))
    (selectBytes sheet (x e)) (selectBytes sheet (x (rightNeighbor e))) T
  intro i L U
  have K : i<grantBase p := by change i<grantBase (params sheet s); unfold grantBase; omega
  have A := (raw_low_pair sheet x e N mask i K).1
  rw [H] at A
  exact A.trans (W i L U)

-- CHECK: ReportOwnerResetDrain.lean:938–951 (same literal extract).
private theorem file_eq_low (p : Params) (u v : BitVec p.w)
    (H : ∀ i,i<grantBase p→u.getLsbD i=v.getLsbD i) :
    drainFile p u=drainFile p v := by
  unfold drainFile
  change (u.extractLsb' (sourceBase p) (19+2*d p)).toNat=
    (v.extractLsb' (sourceBase p) (19+2*d p)).toNat
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  apply H
  unfold grantBase sealBase sourceW
  omega

/-- File holds before ACK, including at its actual source door. The
    old root K0 must still be F/T, and the WAIT opcode must be legal. -/
theorem file_before_ack (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (P : sourcePhase (params sheet s) (selectBytes sheet (x C.root))=2)
    (O : sourceOpcode (params sheet s) (selectBytes sheet (x C.root))≤
      commitOp (params sheet s))
    (T : (publicationToken (params sheet s) true
      (selectBytes sheet (x C.root)) 0).tag=1 ∨
      (publicationToken (params sheet s) true
      (selectBytes sheet (x C.root)) 0).tag=2) :
    drainFile (params sheet s) (selectBytes sheet (rawNext s x e C.root))=
      drainFile (params sheet s) (selectBytes sheet (x C.root)) := by
  let p := params sheet s
  by_cases E : e=C.root
  · subst e
    let u := selectBytes sheet (x C.root)
    let v := selectBytes sheet (x (rightNeighbor C.root))
    have W := drain_row_file_left p (h (rightNeighbor C.root)) u v
    apply Eq.trans _ W
    apply file_eq_low
    intro i J
    have A := (raw_low_pair sheet x C.root N mask i J).1
    rw [C.rootHeader] at A
    exact A
  · by_cases R : rightNeighbor e=C.root
    · let u := selectBytes sheet (x e)
      let v := selectBytes sheet (x C.root)
      have W := lease_row_file_wait_live p (h e) u v P O T
      apply Eq.trans _ W
      apply file_eq_low
      intro i J
      have A := (raw_low_pair sheet x e N mask i J).2
      rw [R,C.rootHeader] at A
      exact A
    · rw [raw_spectator x e C.root (Ne.symm E) (Ne.symm R)]

def HoldTape (sheet : Sheet) (q : Fin n) (j : Fin 3) :
    Raw s n→List (Fin n)→Prop
  | _,[] => True
  | x,e::w => HoldAt sheet x e q j ∧ HoldTape sheet q j (rawNext s x e) w

/-- A tape with no intervening revocation/reuse. Endpoint bit equality
    alone would not establish this. -/
theorem held_run (sheet : Sheet) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q) (N : 1<n)
    (x : Raw s n) (X : Cached sheet hh Q x)
    (q : Fin n) (j : Fin 3) (H : h q=true)
    (O : grantBit sheet x q j=true) (w : List (Fin n))
    (S : HoldTape sheet q j x w) :
    grantBit sheet (rawRun x w) q j=true := by
  induction w generalizing x with
  | nil => exact O
  | cons e w ih =>
    have M := (cached_fibre sheet N hh Q F).mask x X
    have V := (held_step_iff sheet x e q N j M H O).mpr S.1
    exact ih _ ((cached_fibre sheet N hh Q F).closed x e X) V S.2

end L4.ReportLeaseStep
