import Leader.L4.ReportLeaseGrants
import Leader.L4.ReportOwnerProvenanceTransport
import Leader.L4.ReportPrelaunchAllOwners

namespace L4.ReportLeaseOwner
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchAllOwners ReportLeaseGrants ReportJoinedGrants
open ReportByteRows ReportChartPartition ShortChartOwnership BStarShort

variable {s n : Nat} {h : Fin n → Bool}

abbrev Owner (h : Fin n→Bool) := {r : Fin n // h r=true}
noncomputable def charter (G : GapInput h) (r : Owner h) := ownerChart G r.val r.property

theorem unique_cell (hh : ∃ r,h r=true) (G : GapInput h) (i : Fin n) (j : Fin 3) :
    ∃ (r : Owner h) (k : Nat),
      k<(charter G r).L ∧ cell (charter G r) k=(i,j) ∧
      ∀ (q : Owner h) l,l<(charter G q).L → cell (charter G q) l=(i,j) → q=r ∧ l=k :=
  fixed_charts_partition hh G.room
    (fun r R=>by obtain ⟨a,_,B,D⟩ := G.gaps r R; exact ⟨a,B,D⟩)
    (charter G) (fun r=>owner_chart_root G r.val r.property) i j

private theorem non_outgoing_same (d : Sheet) (x : Raw s n) (e i : Fin n)
    (N : 1<n) (D : e≠i) (H : lower d (oldHeaders (rows s) (x i))=true)
    (K : Compatible (rawGrant d x i)) (j : Fin 3) :
    rawGrant d (rawNext s x e) i j=rawGrant d x i j := by
  by_cases R : i=rightNeighbor e
  · subst i
    exact raw_incoming_preserves d x e (edge_sep N e) H K j
  · unfold rawGrant
    rw [ReportRawProjection.raw_spectator x e i (Ne.symm D) R]

/-- Loss of a held canonical lane is charged to the literal old
owner slot bearing a healthy RESET0. No neighbor-only mark can lose it. -/
theorem loss_has_unique_owner_reset (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (N : 1<n)
    (x : Raw s n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (e i : Fin n) (j : Fin 3) (H : h i=true)
    (C : Compatible (rawGrant d x i))
    (Held : rawGrant d x i j=true) (Loss : rawGrant d (rawNext s x e) i j=false) :
    e=i ∧ ∃ (r : Owner h) (k : Nat),
      k<(charter G r).L ∧ cell (charter G r) k=(i,j) ∧
      (tok d (charter G r) x k).tag=2 ∧
      (tok d (charter G r) x k).fault=false ∧
      (tok d (charter G r) x k).opcode=0 ∧
      ∀ (q : Owner h) l,l<(charter G q).L → cell (charter G q) l=(i,j) → q=r ∧ l=k := by
  have Hd : lower d (oldHeaders (rows s) (x i))=true := (mask i).trans H
  have E : e=i := by
    apply Classical.byContradiction
    intro D
    have W := non_outgoing_same d x e i N D Hd C j
    rw [Loss,Held] at W
    contradiction
  subst e
  have R := raw_outgoing_retains_iff d x i (edge_sep N i) Hd C j Held
  rw [Loss] at R
  have Rel : (oldView (params d s) true (selectBytes d (x i))).release j=true := by
    cases K : (oldView (params d s) true (selectBytes d (x i))).release j <;>
      simp [K] at R ⊢
  obtain ⟨r,k,K,A,U⟩ := unique_cell hh G i j
  have S : out (charter G r) k=i := congrArg Prod.fst A
  have P : (charter G r).route.port k=j := congrArg Prod.snd A
  have T : tok d (charter G r) x k=reportK (params d s) true (selectBytes d (x i)) j := by
    rw [ReportOwnerProvenanceTransport.predecessor_projection,S,H,P]
    rfl
  obtain ⟨Tag,Fault,Op⟩ := (release_old_token (params d s) true (selectBytes d (x i)) j).mp Rel
  exact ⟨rfl,r,k,K,A,by rwa [T],by rwa [T],by rwa [T],U⟩

/-- The only way to create a fresh grant at a canonical frozen
header is the actual outgoing mark with a true OLD arbitration win. -/
theorem gain_at_old_win (d : Sheet) (N : 1<n) (x : Raw s n)
    (e i : Fin n) (j : Fin 3)
    (H : lower d (oldHeaders (rows s) (x i))=true)
    (C : Compatible (rawGrant d x i))
    (Empty : rawGrant d x i j=false) (Gain : rawGrant d (rawNext s x e) i j=true) :
    e=i ∧ (oldView (params d s) true (selectBytes d (x i))).win j=true := by
  have E : e=i := by
    apply Classical.byContradiction
    intro D
    have W := non_outgoing_same d x e i N D H C j
    rw [Gain,Empty] at W
    contradiction
  subst e
  exact ⟨rfl,(raw_outgoing_fresh_exact d x i (edge_sep N i) H j Empty).symm.trans Gain⟩

private theorem ask_of_win (g : GrantView) (j : Fin 3) (W : g.win j=true) :
    g.ask j=true := by
  by_cases J : j=1
  · subst j
    simp [GrantView.win,GrantView.centerWin,Bool.and_eq_true] at W
    exact W.1.1.1.1
  · simp [GrantView.win,J,Bool.and_eq_true] at W
    exact W.1.1.2

/-- A new grant is backed by one healthy old ACQUIRE occurrence in
the chart partition, not a grant inferred retroactively from payload. -/
theorem gain_has_unique_owner_acquire (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (N : 1<n) (x : Raw s n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (e i : Fin n) (j : Fin 3) (H : h i=true)
    (C : Compatible (rawGrant d x i))
    (Empty : rawGrant d x i j=false) (Gain : rawGrant d (rawNext s x e) i j=true) :
    e=i ∧ ∃ (r : Owner h) (k : Nat),
      k<(charter G r).L ∧ cell (charter G r) k=(i,j) ∧
      (tok d (charter G r) x k).tag=2 ∧
      (tok d (charter G r) x k).fault=false ∧
      (tok d (charter G r) x k).opcode=acqOp (params d s) ∧
      ∀ (q : Owner h) l,l<(charter G q).L→cell (charter G q) l=(i,j)→q=r ∧ l=k := by
  obtain ⟨E,W⟩ := gain_at_old_win d N x e i j ((mask i).trans H) C Empty Gain
  have A := ask_of_win _ _ W
  change ((reportK _ true (selectBytes d (x i)) j).tag==2 &&
    !(reportK _ true (selectBytes d (x i)) j).fault &&
    (reportK _ true (selectBytes d (x i)) j).opcode==acqOp (params d s))=true at A
  simp only [Bool.and_eq_true,beq_iff_eq] at A
  obtain ⟨r,k,K,L,U⟩ := unique_cell hh G i j
  have Site : out (charter G r) k=i := congrArg Prod.fst L
  have Port : (charter G r).route.port k=j := congrArg Prod.snd L
  have T : tok d (charter G r) x k=reportK (params d s) true (selectBytes d (x i)) j := by
    rw [ReportOwnerProvenanceTransport.predecessor_projection,Site,H,Port]
    rfl
  have Fault : (reportK (params d s) true (selectBytes d (x i)) j).fault=false := by
    have F0 := A.1.2
    cases F : (reportK (params d s) true (selectBytes d (x i)) j).fault <;> simp_all
  exact ⟨E,r,k,K,L,by rw [T]; exact A.1.1,by rw [T]; exact Fault,
    by rw [T]; exact A.2,U⟩

#print axioms unique_cell
#print axioms loss_has_unique_owner_reset
#print axioms gain_at_old_win
#print axioms gain_has_unique_owner_acquire
end L4.ReportLeaseOwner
