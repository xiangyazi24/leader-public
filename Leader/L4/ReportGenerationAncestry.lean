import Leader.L4.ReportLeaseOwner
import Leader.L4.ReportOwnerReverseControl
import Leader.L4.ReportReceiptProvenance
import Leader.L4.ReportRawCommitSnapshot
import Leader.L4.ReportIngressOwnership

namespace L4.ReportGenerationAncestry
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportByteRows ReportOwnerResetDrain
open ReportRawProjection ReportLeaseGrants ReportJoinedGrants
open ReportPrelaunchK1Geometry ReportOwnerProvenanceTransport

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

variable {s n : Nat} {h : Fin n→Bool}

def rawSelector (sheet : Sheet) (x : Raw s n) (i : Fin n) : Nat :=
  publicationSelector (params sheet s) (selectBytes sheet (x i))

def oldCommitAt (sheet : Sheet) (x : Raw s n) (e : Fin n) : Prop :=
  ancestryCommitOpportunity (params sheet s)
    (lower sheet (oldHeaders (rows s) (x e)))
    (lower sheet (oldHeaders (rows s) (x (rightNeighbor e))))
    (selectBytes sheet (x e)) (selectBytes sheet (x (rightNeighbor e)))

private theorem pair_join (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : e≠rightNeighbor e) :
    (selectBytes sheet (rawNext s x e e),
      selectBytes sheet (rawNext s x e (rightNeighbor e))) =
      join (params sheet s)
        (lower sheet (oldHeaders (rows s) (x e)),
          lower sheet (oldHeaders (rows s) (x (rightNeighbor e))))
        (selectBytes sheet (x e),selectBytes sheet (x (rightNeighbor e))) := by
  cases sheet
  · exact raw_report1_pair x e N
  · exact raw_report2_pair x e N

private theorem join_selector (p : Params) (h : Pair Bool) (u v : BitVec p.w) :
    publicationSelector p (join p h (u,v)).1=
      publicationSelector p ((row p h (u,v)).1.apply u) ∧
    publicationSelector p (join p h (u,v)).2=
      publicationSelector p ((row p h (u,v)).2.apply v) := by
  let G := ShortGeo.report p.beta p.digits p.streak
  let i := ancestrySelectorAddr p
  have F : ¬G.owned i := by
    intro H
    have K := H.1
    change reportWidth p.beta p.digits p.streak-ell (max 3 p.digits+1)-1≤i at K
    have W := layout_size p
    change reportWidth p.beta p.digits p.streak=workW p+1+ell (max 3 p.digits+1) at W
    rw [W] at K
    unfold i ancestrySelectorAddr workW at K
    omega
  have H := G.work_agrees_outside (max 3 p.digits) h (u,v)
    (BStarShort.reportWork p h (u,v)) i F
  have L := BStarShort.report_apply_outside p h (u,v) i (.inr (Nat.le_refl _))
  exact ⟨ancestry_selector_bit_congr p _ _ (H.1.trans L),
    ancestry_selector_bit_congr p _ _ H.2⟩

/-- Every mark, with the only exception at the actual old accepted
    candidate ingress of this physical word. -/
theorem raw_selector_frame (sheet : Sheet) (x : Raw s n) (e i : Fin n)
    (N : 1<n) (H : ¬(i=rightNeighbor e ∧ oldCommitAt sheet x e)) :
    rawSelector sheet (rawNext s x e) i=rawSelector sheet x i := by
  let p := params sheet s
  let hu := lower sheet (oldHeaders (rows s) (x e))
  let hv := lower sheet (oldHeaders (rows s) (x (rightNeighbor e)))
  let u := selectBytes sheet (x e)
  let v := selectBytes sheet (x (rightNeighbor e))
  have P := pair_join sheet x e (edge_sep N e)
  have J := join_selector p (hu,hv) u v
  by_cases L : i=e
  · subst i
    unfold rawSelector
    have P0 := congrArg _root_.Prod.fst P
    dsimp only at P0
    rw [P0]
    exact J.1.trans (ancestry_row_selector_left p hu hv u v)
  · by_cases R : i=rightNeighbor e
    · subst i
      have C : ¬ancestryCommitOpportunity p hu hv u v :=
        fun C=>H ⟨rfl,C⟩
      unfold rawSelector
      have P0 := congrArg _root_.Prod.snd P
      dsimp only at P0
      rw [P0]
      exact J.2.trans (ancestry_row_selector_right p hu hv u v C)
    · unfold rawSelector
      rw [raw_spectator x e i L R]

/-- A changed centre selector identifies an actual old COMMIT in the
unique lane-0 ingress cell of this very chart, not in a rival chart.
Only the pending-source provenance of that old token remains to be
proved by the generation induction. -/
theorem changed_centre_owns_ingress
    (sheet : Sheet) (G : GapInput h)
    (r : ReportLeaseOwner.Owner h) (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (changeSel : rawSelector sheet (rawNext s x e) (out (ReportLeaseOwner.charter G r)
        (ReportLeaseOwner.charter G r).a) ≠
      rawSelector sheet x (out (ReportLeaseOwner.charter G r) (ReportLeaseOwner.charter G r).a)) :
    let C := ReportLeaseOwner.charter G r
    C.a-1<C.L ∧ ShortChartOwnership.cell C (C.a-1)=(e,0) ∧
      (tok sheet C x (C.a-1)).fault=false ∧
      (tok sheet C x (C.a-1)).opcode=commitOp (params sheet s) := by
  classical
  let C := ReportLeaseOwner.charter G r
  have A : out C C.a=rightNeighbor e ∧ oldCommitAt sheet x e := by
    apply Classical.byContradiction
    intro H
    exact changeSel (raw_selector_frame sheet x e _ N H)
  obtain ⟨K,F⟩ := ReportIngressOwnership.ingress_cell G r e A.1.symm
  have L := congrArg _root_.Prod.fst F
  have J := congrArg _root_.Prod.snd F
  change out C (C.a-1)=e at L
  change C.route.port (C.a-1)=0 at J
  have B := A.2
  unfold oldCommitAt ancestryCommitOpportunity at B
  rw [mask e] at B
  refine ⟨K,F,?_⟩
  rw [predecessor_projection,L,J]
  exact ⟨B.2.2.1,B.2.2.2.1⟩

/-- On a genuine guarded accepted COMMIT it is the new selected bank
    on THIS mark, not a property deferred to the reply consume. -/
theorem raw_selector_commit (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (H : lower sheet (oldHeaders (rows s) (x (rightNeighbor e)))=true)
    (dsc : Nat)
    (G : CommitGuard (params sheet s) (lower sheet (oldHeaders (rows s) (x e)))
      (selectBytes sheet (x e)) (selectBytes sheet (x (rightNeighbor e))) dsc) :
    rawSelector sheet (rawNext s x e) (rightNeighbor e)=(dsc/4)%2 := by
  have P := congrArg _root_.Prod.snd (pair_join sheet x e (edge_sep N e))
  rw [H] at P
  dsimp only at P
  unfold rawSelector
  rw [P]
  exact (ReportRawCommitSnapshot.join_commit_same_mark _ _ _ _ dsc G).1

theorem raw_selector_commit_ne (sheet : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (H : lower sheet (oldHeaders (rows s) (x (rightNeighbor e)))=true)
    (dsc : Nat)
    (G : CommitGuard (params sheet s) (lower sheet (oldHeaders (rows s) (x e)))
      (selectBytes sheet (x e)) (selectBytes sheet (x (rightNeighbor e))) dsc)
    (D : (dsc/4)%2≠dsc/8) :
    rawSelector sheet (rawNext s x e) (rightNeighbor e)≠
      rawSelector sheet x (rightNeighbor e) := by
  rw [raw_selector_commit sheet x e N H dsc G]
  exact fun E=>D (E.trans G.2.2.1)

/-- Exact old held-bit criterion without assuming canonicality.
    The checked held_exact is its canonical special case. -/
private theorem old_held_no_win (g : BStarShort.GrantView) (j : Fin 3)
    (O : g.old j=true) : g.win j=false := by
  by_cases J : j=1
  · subst j
    simp [BStarShort.GrantView.win,BStarShort.GrantView.centerWin,
      BStarShort.GrantView.canonical,O]
  · cases W : g.old 1 <;>
      simp [BStarShort.GrantView.win,BStarShort.GrantView.canonical,J,W,O]

theorem old_held_exact (g : BStarShort.GrantView) (j : Fin 3)
    (H : g.header=true) (O : g.old j=true) :
    g.nextValue j=true ↔ g.canonical j=true ∧ g.release j=false := by
  simp [BStarShort.GrantView.nextValue,H,old_held_no_win g j O]

def oldIncidence (sheet : Sheet) (x : Raw s n) (i : Fin n) :=
  oldView (params sheet s) true (selectBytes sheet (x i))

def grantSurvives (sheet : Sheet) (x : Raw s n) (e i : Fin n) (j : Fin 3) : Prop :=
  if i=e then
    (oldIncidence sheet x i).canonical j=true ∧
      (oldIncidence sheet x i).release j=false
  else if i=rightNeighbor e then
    (oldIncidence sheet x i).canonical j=true
  else True

theorem held_grant_survives_iff (sheet : Sheet) (x : Raw s n) (e i : Fin n)
    (j : Fin 3) (N : 1<n)
    (Hdr : lower sheet (oldHeaders (rows s) (x i))=true)
    (Held : rawGrant sheet x i j=true) :
    rawGrant sheet (rawNext s x e) i j=true ↔ grantSurvives sheet x e i j := by
  by_cases L : i=e
  · subst i
    have V := (raw_grant_rows sheet x e (edge_sep N e) j).1
    rw [V,Hdr]
    simpa [grantSurvives,oldIncidence] using
      old_held_exact (oldIncidence sheet x e) j rfl Held
  · by_cases R : i=rightNeighbor e
    · subst i
      have V := (raw_grant_rows sheet x e (edge_sep N e) j).2
      rw [V,Hdr,if_pos rfl]
      simp [grantSurvives,L,oldIncidence]
    · unfold rawGrant
      rw [raw_spectator x e i L R]
      simp only [grantSurvives,L,R,if_false,iff_true]
      exact Held

/-- Proof-only number and cursor; neither is encoded in the raw
    constant-state protocol. Faults may be owned by the command even
    when their canonical opcode is zero. -/
inductive CommandRail where
  | issue
  | forward (k : Nat) (packet : Tok)
  | reverse (k : Nat) (reply : Tok)

structure GenerationTag where
  number : Nat
  selected : Nat
  op : Nat
  rail : CommandRail
  -- capture at centre can precede successful source ACQ consume
  centreWon : Bool
  fileInstalled : Bool
  held : Nat→Bool
  heldSeal : Option Nat

def centre (C : Chart h) : Fin n := out C C.a

def sourceBytes (sheet : Sheet) (C : Chart h) (x : Raw s n) :=
  selectBytes sheet (x C.root)

def railState (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (g : GenerationTag) : Prop :=
  let pc := controlWork (params sheet s) (sourceBytes sheet C x)
  match g.rail with
  | .issue =>
      pc=(1,g.op) ∧ ∀ i,i<C.L→tok sheet C x i=MISByteCodec.E
  | .forward k packet =>
      pc=(2,g.op) ∧ k<C.L ∧ packet.tag=2 ∧
      (packet.fault=false→packet.opcode=g.op) ∧
      (∀ i,i<C.L→tok sheet C x i=
        if i<k then MISByteCodec.T else if i=k then packet else MISByteCodec.E)
  | .reverse k reply =>
      pc=(2,g.op) ∧ k<C.L ∧ reply.tag=3 ∧
      (reply.fault=false→reply.opcode=g.op) ∧
      (∀ i,i<C.L→tok sheet C x i=
        if i<k then MISByteCodec.T else if i=k then reply else MISByteCodec.E)

def WriteCommand (p : Params) (t : Tok) : Prop :=
  t.tag=2 ∧ t.fault=false ∧ writeOp p≤t.opcode ∧ t.opcode<sealOp p

/-- Current-state, pre-end portion. The last conjunct is payload
    lineage, not an assumption that the actual selected digit is safe.
    The ghost ledger is updated by the old literal wins/releases. -/
structure GenerationInv (sheet : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (x : Raw s n) (g : GenerationTag) : Prop where
  cached : Cached sheet hh Q x
  centreIndex : C.a<C.L
  centreHeader : h (centre C)=true
  centreLane : C.route.port C.a=1
  selectedBound : g.selected<2
  selector : rawSelector sheet x (centre C)=g.selected
  rail : railState sheet C x g
  grants : ∀ k,k<C.L→h (out C k)=true→
    rawGrant sheet x (out C k) (C.route.port k)=g.held k
  canonicalHeld : ∀ k,k<C.L→h (out C k)=true→g.held k=true→
    Compatible (rawGrant sheet x (out C k))
  won : g.centreWon=true→g.held C.a=true
  installed : g.fileInstalled=true→g.centreWon=true ∧
    ancestrySourceCentre (params sheet s) (sourceBytes sheet C x)=g.selected
  sealBytes : reportOldSeal (params sheet s) (selectBytes sheet (x (centre C)))=g.heldSeal
  writes : ∀ k,k<C.L→WriteCommand (params sheet s) (tok sheet C x k) →
    g.fileInstalled=true ∧
    ∃ q<2^(2*d (params sheet s)),
      (tok sheet C x k).payload=ancestryWritePayload (params sheet s) g.selected q

/-- The precise mathematical consequence of the current-state
    payload ancestry; it is independent of nonheader grant bits. -/
theorem generated_write_inactive (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (Q : Raw s n→Prop) (x : Raw s n) (g : GenerationTag)
    (I : GenerationInv sheet C hh Q x g)
    (k : Nat) (K : k<C.L) (W : WriteCommand (params sheet s) (tok sheet C x k)) :
    ancestryWriteOld (params sheet s) (tok sheet C x k)=rawSelector sheet x (centre C) ∧
    ancestryWriteTarget (params sheet s) (tok sheet C x k)≠rawSelector sheet x (centre C) := by
  obtain ⟨_,q,Q0,P⟩ := I.writes k K W
  obtain ⟨A,B⟩ := ancestry_write_indices _ _ _ q I.selectedBound Q0 P
  rw [I.selector,A,B]
  exact ⟨rfl,by have L := I.selectedBound; omega⟩

/-- The old canonical grant is still owned unless this exact mark
    releases it. This is the all-mark neighbouring-frame specialization
    of the stronger iff above. -/
theorem generation_grant_keep (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (Q : Raw s n→Prop) (x : Raw s n) (g : GenerationTag)
    (I : GenerationInv sheet C hh Q x g)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (N : 1<n) (e : Fin n) (k : Nat) (K : k<C.L)
    (Hdr : h (out C k)=true) (Held : g.held k=true)
    (NoRelease : e=out C k →
      (oldIncidence sheet x (out C k)).release (C.route.port k)=false) :
    rawGrant sheet (rawNext s x e) (out C k) (C.route.port k)=true := by
  let i := out C k
  let j := C.route.port k
  have O : rawGrant sheet x i j=true := (I.grants k K Hdr).trans Held
  have A : (oldIncidence sheet x i).canonical j=true :=
    (canonical_eq _ (I.canonicalHeld k K Hdr Held) j).trans O
  apply (held_grant_survives_iff sheet x e i j N ((mask i).trans Hdr) O).mpr
  unfold grantSurvives
  by_cases E : i=e
  · rw [if_pos E]
    exact ⟨A,NoRelease E.symm⟩
  · rw [if_neg E]
    by_cases R : i=rightNeighbor e
    · rw [if_pos R]
      exact A
    · rw [if_neg R]
      trivial

/-- Prefix induction for the selector, using the literal no-ingress
    condition on each prefix of the SAME raw tape. This condition
    must be derived from serial ownership, not taken as Good8. -/
theorem selector_prefix (sheet : Sheet) (N : 1<n) (x : Raw s n)
    (i : Fin n) (w : List (Fin n))
    (NoCommit : ∀ pre e suf, w=pre++e::suf →
      ¬(i=rightNeighbor e ∧ oldCommitAt sheet (rawRun x pre) e)) :
    rawSelector sheet (rawRun x w) i=rawSelector sheet x i := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have H := NoCommit [] e w rfl
    change ¬(i=rightNeighbor e ∧ oldCommitAt sheet x e) at H
    have A := raw_selector_frame sheet x e i N H
    change rawSelector sheet (rawRun (rawNext s x e) w) i=_
    rw [ih (rawNext s x e) ?_,A]
    intro pre f suf E
    have E0 : e::w=(e::pre)++f::suf := by simp [E]
    exact NoCommit (e::pre) f suf E0

end L4.ReportGenerationAncestry
