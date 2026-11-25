import Leader.L4.ReportSnapshotLease

namespace L4.ReportProtectedAB
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportRawProjection ReportGenerationAncestry ReportLeaseStep
open ReportReaderSelectorLease ReportLeaseGrants ReportGrantTimeline

variable {s n : Nat} {h : Fin n→Bool}

def selectedA (d : Sheet) (x : Raw s n) (i : Fin n) : Bool :=
  publicationA (params d s) (selectBytes d (x i)) (rawSelector d x i)

def selectedB (d : Sheet) (x : Raw s n) (i : Fin n) : Nat :=
  publicationPair (params d s) (selectBytes d (x i)) (rawSelector d x i)

/-- No publication at the queried header: selected A and selected B
both retain their old bytes, even when this mark paints old B into Z. -/
theorem raw_ab_without_ingress (d : Sheet) (N : 1<n)
    (x : Raw s n) (e i : Fin n) (No : ¬(i=rightNeighbor e ∧ oldCommitAt d x e)) :
    selectedA d (rawNext s x e) i=selectedA d x i ∧
      selectedB d (rawNext s x e) i=selectedB d x i := by
  let p := params d s
  let u := selectBytes d (x e)
  let v := selectBytes d (x (rightNeighbor e))
  let mask := fun j=>lower d (oldHeaders (rows s) (x j))
  let sel := rawSelector d x i
  unfold selectedA selectedB
  rw [raw_selector_frame d x e i N No]
  apply ab_bit_congr p _ _ sel
  intro j J
  let a := abAddress p sel j
  have K := raw_low_pair d x e N (h:=mask) (fun _=>rfl) a (ab_bits_below_grants p sel j J)
  by_cases L : i=e
  · subst i
    exact K.1.trans (report_row_left_ab_bits p (mask e) (mask (rightNeighbor e)) u v sel j J)
  · by_cases R : i=rightNeighbor e
    · subst i
      exact K.2.trans (report_row_right_ab_bits p (mask e) (mask (rightNeighbor e)) u v
        (fun T=>No ⟨rfl,T⟩) sel j J)
    · rw [raw_spectator x e i L R]

private theorem held_excludes_ingress (d : Sheet) (x : Raw s n) (e i : Fin n)
    (j : Fin 3) (Side : j=0 ∨ j=2) (C : Compatible (rawGrant d x i))
    (Held : rawGrant d x i j=true) :
    ¬(i=rightNeighbor e ∧ oldCommitAt d x e) := by
    rintro ⟨rfl,Cmd⟩
    have W : rawGrant d x (rightNeighbor e) 1=true := by
      have H := Cmd.2.2.2.2
      unfold packetCommitGuard at H
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp H).1).1).2
    have K : rawGrant d x (rightNeighbor e) j=false :=
      Side.elim (fun J=>J ▸ (C W).1) (fun J=>J ▸ (C W).2)
    exact Bool.noConfusion (Held.symm.trans K)

theorem ab_reader_held_run (d : Sheet) (N : 1<n) (i : Fin n) (j : Fin 3)
    (Side : j=0 ∨ j=2) (x : Raw s n) (w : List (Fin n))
    (C : Compatible (rawGrant d x i)) (Held : HeldAlong d i j x w) :
    selectedA d (rawRun x w) i=selectedA d x i ∧
      selectedB d (rawRun x w) i=selectedB d x i := by
  induction w generalizing x with
  | nil => exact ⟨rfl,rfl⟩
  | cons e w IH =>
    have No := held_excludes_ingress d x e i j Side C Held.1
    have F := raw_ab_without_ingress d N x e i No
    have G := raw_compatible_step d x e i (edge_sep N e) C
    obtain ⟨X,Y⟩ := IH _ G Held.2
    exact ⟨X.trans F.1,Y.trans F.2⟩


open ReportOwnerIssueControl ReportOwnerAcquireReturn ReportAcquireAllCaptures
open ReportOwnerAcquireProvenance (BeforeConsume NoConsume)
open ReportPrelaunchClock ReportOwnerSerial ReportIndexedSideLease ReportGoodEightCut ReportLeaseOwner

variable {Q : Raw s n→Prop}

private theorem acq_A_from_prefix (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0)
    (A : ReportOwnerAcquireProvenance.FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (i : Nat) (I : i<C.L) (H : h (out C i)=true)
    (Side : C.route.port i=0 ∨ C.route.port i=2)
    (Compat : Compatible (rawGrant d x0 (out C i)))
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (u : List (Fin n)) (P : u <+: w)
    (Held : rawGrant d (rawRun x0 u) (out C i) (C.route.port i)=true) :
    selectedA d (rawRun x0 w) (out C i)=selectedA d (rawRun x0 u) (out C i) := by
  induction T generalizing u with
  | nil => rw [P.eq_of_length_le (Nat.zero_le _)]
  | @snoc ws e prev nc IH =>
    by_cases L : u.length≤ws.length
    · have Prefix := List.prefix_of_prefix_length_le P (List.prefix_append ws [e]) L
      have Held0 := ReportAcquireWinHold.acq_grant_from_prefix d C hh G F N x0 X A digit i I H Compat
        ws prev u Prefix Held
      have Comp := ReportAcquireWinHold.compatible_run d N x0 (out C i) Compat ws
      have No := held_excludes_ingress d (rawRun x0 ws) e (out C i) (C.route.port i) Side Comp Held0
      rw [ShortOwnerEpochJS.raw_snoc]
      exact (raw_ab_without_ingress d N _ e _ No).1.trans (IH u Prefix Held)
    · rw [P.eq_of_length_le (by simp; omega)]

/-- The authentic READ-side A-bit at the actual ACQ win equals that
neighbor's current selected A on the old mark of the later COMMIT. -/
theorem captured_A_now (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (issue : Raw s n) (X : Cached d hh Q issue)
    (I : LegalIssue d C issue) (P : readPC d C issue=(1,acqOp (params d s)))
    (Compat : ∀ i,h i=true→Compatible (rawGrant d issue i))
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s issue (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s issue (door C)) w) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s issue (door C)) w) 0).outcome≠1)
    (v : List (Fin n))
    (NR : NoRestartTape d C (rawNext s (rawRun (rawNext s issue (door C)) w) (door C)) v)
    (i : Nat) (J : i<C.L) (H : h (out C i)=true)
    (Side : C.route.port i=0 ∨ C.route.port i=2) :
    let b := rawNext s (rawRun (rawNext s issue (door C)) w) (door C)
    acqCaptureHeader (params d s) (selectBytes d (b C.root))/2^(2-(C.route.port i).val)%2=
      (selectedA d (rawRun b v) (out C i)).toNat := by
  dsimp only
  let x0 := rawNext s issue (door C)
  let old := rawRun x0 w
  let b := rawNext s old (door C)
  have Caps := all_captures_after_consume d C hh G F N issue X I P Compat digit w T Tag ND [] trivial
  have Hold := (all_captures_after_consume d C hh G F N issue X I P Compat digit w T Tag ND v NR).2.2.2 i J H
  obtain ⟨u,z,q,S,_,_,Won,_,Val⟩ := captured_file_fields d C x0 b w i (Caps.2.2.2 i J H).1
  obtain ⟨X0,F0⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N issue X I P
  have C0 := raw_compatible_step d issue (door C) (out C i) (edge_sep N _) (Compat _ H)
  have Pre : (u++[out C i]) <+: w := by rw [S]; simp
  have Won' : rawGrant d (rawRun x0 (u++[out C i])) (out C i) (C.route.port i)=true := by
    rw [ShortOwnerEpochJS.raw_snoc]
    exact Won
  have G0 := ReportAcquireWinHold.acq_grant_from_prefix d C hh G F N x0 X0 F0 digit i J H C0 w T _ Pre Won'
  have Eq := acq_A_from_prefix d C hh G F N x0 X0 F0 digit i J H Side C0 w T _ Pre Won'
  rw [ShortOwnerEpochJS.raw_snoc] at Eq
  have Comp := ReportAcquireWinHold.compatible_run d N x0 (out C i) C0 w
  have Step := (raw_ab_without_ingress d N old (door C) (out C i)
    (held_excludes_ingress d old (door C) (out C i) _ Side Comp G0)).1
  have WinStep := (raw_ab_without_ingress d N (rawRun x0 u) (out C i) (out C i)
    (fun M=>edge_sep N _ M.1)).1
  have CB := raw_compatible_step d old (door C) (out C i) (edge_sep N _) Comp
  have Frame := (ab_reader_held_run d N (out C i) _ Side b v CB Hold.2).1
  have Same := Frame.trans (Step.trans (Eq.trans WinStep))
  exact Val.trans (congrArg Bool.toNat Same).symm

#print axioms captured_A_now
#print axioms raw_ab_without_ingress
#print axioms ab_reader_held_run
end L4.ReportProtectedAB
