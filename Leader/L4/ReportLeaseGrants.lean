import Leader.L4.ReportJoinedGrants
import Leader.L4.ReportResetRawHooks

namespace L4.ReportLeaseGrants
open L4.BStarShort L4.ReportByteRows L4.ReportJoinedGrants

/-- Writer and either reader cannot share a canonical grant triple. -/
def Compatible (g : Fin 3 → Bool) : Prop :=
  g 1=true → g 0=false ∧ g 2=false

theorem canonical_eq (g : GrantView) (H : Compatible g.old) (j : Fin 3) :
    g.canonical j=g.old j := by
  by_cases W : g.old 1=true
  · obtain ⟨L,R⟩ := H W
    have J : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases J with rfl|rfl|rfl <;> simp [GrantView.canonical,W,L,R]
  · have W' : g.old 1=false := Bool.eq_false_iff.mpr W
    simp [GrantView.canonical,W']

theorem canonical_compatible (g : GrantView) : Compatible g.canonical := by
  have E : g.canonical 1=g.old 1 := by cases H : g.old 1 <;> simp [GrantView.canonical,H]
  intro H
  rw [E] at H
  simp [GrantView.canonical,H]

theorem next_compatible (g : GrantView) : Compatible g.nextValue := by
  intro H
  cases C : g.header
  · simp [GrantView.nextValue,C] at H
  · have HH : ((g.canonical 1 && !g.release 1) || g.centerWin) = true := by
      simpa [GrantView.nextValue,GrantView.win,C] using H
    have HH' : (g.canonical 1 && !g.release 1)=true ∨ g.centerWin=true := by simpa only [Bool.or_eq_true] using HH
    rcases HH' with HH|HH
    · have W : g.canonical 1=true := ((Bool.and_eq_true _ _).mp HH).1
      obtain ⟨L,R⟩ := canonical_compatible g W
      constructor <;> simp [GrantView.nextValue,GrantView.win,C,W,L,R]
    · have T := HH
      simp only [GrantView.centerWin, Bool.and_eq_true] at T
      have L : g.canonical 0=false := by simpa using T.1.1.2
      have R : g.canonical 2=false := by simpa using T.2
      constructor <;> simp [GrantView.nextValue,GrantView.win,C,L,R,HH]

theorem held_exact (g : GrantView) (Hdr : g.header=true) (H : Compatible g.old)
    (j : Fin 3) (Old : g.old j=true) : g.nextValue j = !g.release j := by
  have C : g.canonical j=true := (canonical_eq g H j).trans Old
  have W : g.win j=false := by
    by_cases J : j=1
    · subst j
      simp [GrantView.win,GrantView.centerWin,C]
    · simp [GrantView.win,J,C]
  simp [GrantView.nextValue,Hdr,C,W]

theorem fresh_exact (g : GrantView) (Hdr : g.header=true) (j : Fin 3)
    (Old : g.old j=false) : g.nextValue j = g.win j := by
  have C : g.canonical j=false := by
    by_cases J : j=1
    · subst j; simp [GrantView.canonical,Old]
    · simp [GrantView.canonical,J,Old]
  simp [GrantView.nextValue,Hdr,C]

/-- The old-snapshot arbiter does not hand the writer a lease on the
    same mark as receipt/release of a reader's old lease. -/
theorem reader_blocks_center_win (g : GrantView) (H : Compatible g.old)
    (j : Fin 3) (R : j≠1) (Old : g.old j=true) : g.win 1=false := by
  have J : j=0 ∨ j=1 ∨ j=2 := by omega
  have C : g.canonical j=true := (canonical_eq g H j).trans Old
  rcases J with rfl|rfl|rfl
  · simp [GrantView.win,GrantView.centerWin,C]
  · exact (R rfl).elim
  · simp [GrantView.win,GrantView.centerWin,C]

/-- Even a releasing writer prevents a same-mark old-reader win. -/
theorem center_blocks_reader_win (g : GrantView) (H : Compatible g.old)
    (j : Fin 3) (R : j≠1) (Old : g.old 1=true) : g.win j=false := by
  have C : g.canonical 1=true := (canonical_eq g H 1).trans Old
  simp [GrantView.win,R,C]

theorem recv_canonical (p : Params) (h : Bool) (u : BitVec p.w) (j : Fin 3) :
    grantReceived p h u j=if h then (oldView p h u).canonical j else false := rfl

theorem incoming_preserves (p : Params) (u : BitVec p.w)
    (H : Compatible (oldView p true u).old) (j : Fin 3) :
    grantReceived p true u j=u.getLsbD (grantAddr p j) := by
  exact canonical_eq (oldView p true u) H j

open L4.AllSizeProtocol L4.PhysicalCustody L4.ReportResetRawHooks

def bytesGrant (p : Params) (u : BitVec p.w) (j : Fin 3) : Bool :=
  u.getLsbD (grantAddr p j)

def rawGrant (d : Sheet) {s n : Nat} (x : Raw s n) (i : Fin n) (j : Fin 3) : Bool :=
  bytesGrant (params d s) (selectBytes d (x i)) j

/-- Both actual raw endpoints, for either sheet. The incumbent header
    argument is always the old header; frozen-lower equality is separate. -/
theorem raw_grant_rows (d : Sheet) {s n : Nat} (x : Raw s n) (e : Fin n)
    (N : e≠rightNeighbor e) (j : Fin 3) :
    let p := params d s
    let v := rightNeighbor e
    let hu := lower d (oldHeaders (rows s) (x e))
    let hv := lower d (oldHeaders (rows s) (x v))
    rawGrant d (rawNext s x e) e j=(oldView p hu (selectBytes d (x e))).nextValue j ∧
    rawGrant d (rawNext s x e) v j=(if hv then
      (oldView p hv (selectBytes d (x v))).canonical j else false) := by
  dsimp only
  have E : rawGrant d (rawNext s x e) e j=grantNext (params d s)
      (lower d (oldHeaders (rows s) (x e))) (selectBytes d (x e)) j ∧
      rawGrant d (rawNext s x e) (rightNeighbor e) j=grantReceived (params d s)
      (lower d (oldHeaders (rows s) (x (rightNeighbor e)))) (selectBytes d (x (rightNeighbor e))) j := by
    cases d
    · exact service_joined_grants_report1 x e N j
    · exact service_joined_grants_report2 x e N j
  exact ⟨E.1.trans (next_agrees _ _ _ _).symm,E.2.trans (recv_canonical _ _ _ _)⟩

theorem raw_incoming_preserves (d : Sheet) {s n : Nat} (x : Raw s n) (e : Fin n)
    (N : e≠rightNeighbor e) (Hdr : lower d (oldHeaders (rows s) (x (rightNeighbor e)))=true)
    (H : Compatible (rawGrant d x (rightNeighbor e))) (j : Fin 3) :
    rawGrant d (rawNext s x e) (rightNeighbor e) j=rawGrant d x (rightNeighbor e) j := by
  have D := (raw_grant_rows d x e N j).2
  rw [D,Hdr,if_pos rfl]
  exact canonical_eq _ H j

theorem raw_outgoing_retains_iff (d : Sheet) {s n : Nat} (x : Raw s n) (e : Fin n)
    (N : e≠rightNeighbor e) (Hdr : lower d (oldHeaders (rows s) (x e))=true)
    (H : Compatible (rawGrant d x e)) (j : Fin 3) (Held : rawGrant d x e j=true) :
    rawGrant d (rawNext s x e) e j=
      !(oldView (params d s) true (selectBytes d (x e))).release j := by
  have D := (raw_grant_rows d x e N j).1
  rw [D,Hdr]
  exact held_exact _ rfl H j Held

/-- Once canonical, each site's lease arbitration stays canonical on any
    raw mark. Endpoints are distinct; no observer or fixed layout is used. -/
theorem raw_compatible_step (d : Sheet) {s n : Nat} (x : Raw s n) (e i : Fin n)
    (N : e≠rightNeighbor e) (I : Compatible (rawGrant d x i)) :
    Compatible (rawGrant d (rawNext s x e) i) := by
  by_cases L : i=e
  · subst i
    have E : rawGrant d (rawNext s x e) e =
        (oldView (params d s) (lower d (oldHeaders (rows s) (x e)))
          (selectBytes d (x e))).nextValue :=
      funext fun j => (raw_grant_rows d x e N j).1
    rw [E]
    exact next_compatible _
  · by_cases R : i=rightNeighbor e
    · subst i
      let hv := lower d (oldHeaders (rows s) (x (rightNeighbor e)))
      let g := oldView (params d s) hv (selectBytes d (x (rightNeighbor e)))
      have E : rawGrant d (rawNext s x e) (rightNeighbor e) =
          (if hv then g.canonical else fun _ => false) := by
        funext j
        have D := (raw_grant_rows d x e N j).2
        change _ = if hv then g.canonical j else false at D
        split <;> rename_i K <;> simpa [K] using D
      rw [E]
      split
      · exact canonical_compatible _
      · intro H; contradiction
    · have E := ReportRawProjection.raw_spectator x e i L R
      unfold rawGrant
      rw [E]
      exact I

/-- Pending/proof-only lease claims cannot identify arbitrary old true
    reader bits with retained authority before canonicalization. -/
theorem dirty_incumbent_reader_cleared (g : GrantView) (R : g.old 0=true)
    (W : g.old 1=true) : ¬Compatible g.old ∧ g.canonical 0=false := by
  exact ⟨fun H => Bool.noConfusion ((H W).1.symm.trans R),
    by simp [GrantView.canonical,W]⟩

theorem raw_outgoing_fresh_exact (d : Sheet) {s n : Nat} (x : Raw s n) (e : Fin n)
    (N : e≠rightNeighbor e) (Hdr : lower d (oldHeaders (rows s) (x e))=true)
    (j : Fin 3) (Empty : rawGrant d x e j=false) :
    rawGrant d (rawNext s x e) e j=
      (oldView (params d s) true (selectBytes d (x e))).win j := by
  have D := (raw_grant_rows d x e N j).1
  rw [D,Hdr]
  exact fresh_exact _ rfl j Empty

/-- The release read is from the same old owner lane, not from a
    neighbour's token or post-route packet. Header readiness for RESET
    is automatic in the grant view; its actual byte equivalence is
    `grant_old_view_bridge`. -/
theorem release_old_token (p : Params) (h : Bool) (u : BitVec p.w) (j : Fin 3) :
    (oldView p h u).release j=true ↔
      (reportK p h u j).tag=2 ∧ (reportK p h u j).fault=false ∧ (reportK p h u j).opcode=0 := by
  change ((_ == 2) && !_ && (_ == 0)) = true ↔ _
  simp [Bool.and_eq_true, beq_iff_eq, and_assoc]

end L4.ReportLeaseGrants
