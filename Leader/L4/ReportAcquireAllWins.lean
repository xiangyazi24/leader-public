import Leader.L4.ReportOwnerAcquireProvenance

namespace L4.ReportAcquireAllWins
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerReverseShape ReportOwnerReverseControl ReportOwnerAcquireProvenance
open ReportLeaseGrants ReportJoinedGrants
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- Denial at any header lane erases success bit six. -/
theorem header_success_implies_win (p : Params) (u : BitVec p.w) (j : Fin 3)
    (q : Nat) (Q : q<128) (S : acqFlightNext p true u j q/64=1) :
    acqFlightWin p true u j=true := by
  cases W : acqFlightWin p true u j
  · unfold acqFlightNext at S
    simp only [W,if_true,Bool.false_eq_true,if_false] at S
    change (if (q >>> 6)%2==1 then q-64 else q)/64=1 at S
    rw [Nat.shiftRight_eq_div_pow] at S
    change (if (q/64)%2==1 then q-64 else q)/64=1 at S
    split at S
    · omega
    · rename_i H
      simp [beq_iff_eq] at H
      omega
  · rfl

def WonAt (d : Sheet) (C : Chart h) (x0 : Raw s n) (w : List (Fin n)) (i : Nat) : Prop :=
  ∃ pre post : List (Fin n), ∃ q : Nat,
    w=pre++(out C i::post) ∧
    let z := rawRun x0 pre
    FState d C z i q ∧
    acqFlightWin (params d s) true (selectBytes d (z (out C i))) (C.route.port i)=true ∧
    rawGrant d (rawNext s z (out C i)) (out C i) (C.route.port i)=true

private theorem won_snoc (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (e : Fin n) (i : Nat) (W : WonAt d C x0 w i) :
    WonAt d C x0 (w++[e]) i := by
  obtain ⟨pre,post,q,L,R,S,A⟩ := W
  exact ⟨pre,post++[e],q,by rw [L,List.append_assoc]; rfl,R,S,A⟩

def AllWinsFlightAt (d : Sheet) (C : Chart h) (x0 : Raw s n) (w : List (Fin n)) : Prop :=
  (∃ k q,FState d C (rawRun x0 w) k q ∧
    (q/64=1 → ∀ i,i<k→h (out C i)=true→WonAt d C x0 w i)) ∨
  (∃ k q,DState d C (rawRun x0 w) k q ∧
    (q/64=1 → ∀ i,i<C.L→h (out C i)=true→WonAt d C x0 w i))

private theorem append_winner (d : Sheet) (C : Chart h)
    (N : 1<n) (x0 : Raw s n) (w : List (Fin n))
    (mask : ∀ i,lower d (oldHeaders (rows s) (rawRun x0 w i))=h i)
    (k q : Nat) (R : FState d C (rawRun x0 w) k q)
    (Old : q/64=1 → ∀ i,i<k→h (out C i)=true→WonAt d C x0 w i)
    (S : stepPayload d C (rawRun x0 w) k q/64=1)
    (i : Nat) (I : i<k+1) (Hdr : h (out C i)=true) :
    WonAt d C x0 (w++[out C k]) i := by
  let p := params d s
  let z := rawRun x0 w
  let e := out C k
  by_cases K : i=k
  · subst i
    change acqFlightNext p (h e) (selectBytes d (z e)) (C.route.port k) q/64=1 at S
    rw [Hdr] at S
    have W := header_success_implies_win p (selectBytes d (z e)) (C.route.port k) q R.bound S
    have E := (raw_grant_rows d z e (edge_sep N e) (C.route.port k)).1
    rw [mask e,Hdr,next_agrees] at E
    exact ⟨w,[],q,rfl,R,W,E.trans (acqFlight_win_grant p _ _ W)⟩
  · have A := acqFlight_next_spec p (h e) (selectBytes d (z e)) (C.route.port k) q R.bound
    exact won_snoc d C x0 w e i (Old (A.2.1 S) i (by omega) Hdr)

theorem all_wins_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (w : List (Fin n))
    (X : Cached d hh Q (rawRun x0 w)) (A : AllWinsFlightAt d C x0 w)
    (digit : 0<(params d s).digits) (e : Fin n)
    (NC : NoConsume d C (rawRun x0 w) e) :
    AllWinsFlightAt d C x0 (w++[e]) := by
  let x := rawRun x0 w
  let CF := cached_fibre d N hh Q F
  have E : rawRun x0 (w++[e])=rawNext s x e :=
    ShortOwnerEpochJS.raw_snoc x0 w e
  rcases A with ⟨k,q,R,H⟩|⟨k,q,R,H⟩
  · rcases F_step d C hh G F N x X k q R e with A|⟨J,A⟩|⟨J,T,A⟩
    · left
      exact ⟨k,q,E ▸ A,fun S i I Hd=>won_snoc d C x0 w e i (H S i I Hd)⟩
    · subst e
      left
      refine ⟨k+1,stepPayload d C x k q,?_,?_⟩
      · rw [E]; exact A
      · intro S i I Hd
        exact append_winner d C N x0 w (CF.mask x X) k q R H S i I Hd
    · subst e
      right
      refine ⟨k,stepPayload d C x k q,?_,?_⟩
      · rw [E]; exact A
      · intro S i I Hd
        exact append_winner d C N x0 w (CF.mask x X) k q R H S i (by omega) Hd
  · rcases D_step d C hh G F N x X k q R digit e NC with A|⟨j,_,_,A⟩
    · right
      exact ⟨k,q,E ▸ A,fun S i I Hd=>won_snoc d C x0 w e i (H S i I Hd)⟩
    · right
      exact ⟨j,q,E ▸ A,fun S i I Hd=>won_snoc d C x0 w e i (H S i I Hd)⟩

theorem all_wins_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w) :
    Cached d hh Q (rawRun x0 w) ∧ AllWinsFlightAt d C x0 w := by
  induction T with
  | nil =>
    exact ⟨X,.inl ⟨0,64,A,fun _ i I _=>(by omega : False).elim⟩⟩
  | @snoc w e T NC IH =>
    constructor
    · rw [ShortOwnerEpochJS.raw_snoc]
      exact (cached_fibre d N hh Q F).closed _ e IH.1
    · exact all_wins_step d C hh G F N x0 w IH.1 IH.2 digit e NC

/-- Every header occurrence traversed by this same successful command
has a literal old winning departure witness on the original tape. -/
theorem successful_root_all_wins (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (Tag : (tok d C (rawRun x0 w) 0).tag=3)
    (ND : (tok d C (rawRun x0 w) 0).outcome≠1) :
    ∀ i,i<C.L→h (out C i)=true→WonAt d C x0 w i := by
  obtain ⟨_,H⟩ := all_wins_run d C hh G F N x0 X A digit w T
  rcases H with ⟨k,q,R,_⟩|⟨k,q,R,W⟩
  · rw [R.shape.2.2 0 C.positive] at Tag
    unfold frontTag at Tag
    split at Tag <;> try contradiction
    split at Tag <;> contradiction
  · have K : k=0 := by
      by_cases K : k=0
      · exact K
      · rw [R.shape.2.2 0 C.positive] at Tag
        simp [backTag,show 0<k by omega] at Tag
    subst k
    have ND0 : (acqFlightD (params d s) q).outcome≠1 := by rwa [←R.packet]
    have P := acqFlight_D_success (params d s) q R.bound ND0
    exact W P.1

theorem successful_root_lane0 (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (Tag : (tok d C (rawRun x0 w) 0).tag=3)
    (ND : (tok d C (rawRun x0 w) 0).outcome≠1) :
    ∃ pre post : List (Fin n), ∃ q : Nat,
      w=pre++(C.root::post) ∧
      let z := rawRun x0 pre
      FState d C z 0 q ∧
      acqFlightWin (params d s) true (selectBytes d (z C.root)) 0=true ∧
      rawGrant d (rawNext s z C.root) C.root 0=true := by
  have H := successful_root_all_wins d C hh G F N x0 X A digit w T Tag ND
    0 C.positive C.rootHeader
  obtain ⟨u,v,q,E,J,Win,Held⟩ := H
  have Rp : C.route.port 0=0 := C.rootPort
  have R : out C 0=C.root := rfl
  exact ⟨u,v,q,by simpa only [R] using E,J,by simpa only [R,Rp] using Win,
    by simpa only [R,Rp] using Held⟩

end L4.ReportAcquireAllWins
