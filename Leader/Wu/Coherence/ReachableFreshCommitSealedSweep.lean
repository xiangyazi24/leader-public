import Leader.Wu.Coherence.ReachableSoundFresh
import Leader.Wu.Coherence.ReachableCommitOverlap
import Leader.Wu.Coherence.ReachableSealed
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace R2CoherenceV31ReachableFreshBranches1
open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3 R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31MainClearTruth R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear R2CoherenceV31ReachableSoundFresh
variable {n ψ κ τ : Nat}

private theorem gp (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label) (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k = R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]
private theorem pp (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label) (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k = R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val-k) = R2Coherence.back ring i ((raw (C i)).label.val-k)
  rw [h i]
private theorem foot (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label) (o p : Fin n)
    (h : InOpenRFreshFootprintV31 ring D o p) : InOpenRFreshFootprintV31 ring C o p := by
  rcases h with ⟨j,ko,q,ho,kD,hp⟩; rw [gp ring hL j ko.val] at ho
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hf : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val=f := by simpa [f] using gp ring hL j q.val
  have hv : (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val=(raw (C f)).label.val := by
    rw [hf]; exact congrArg Fin.val (hL f)
  let kC : Fin ((raw (C f)).label.val+1) := ⟨kD.val, by simpa only [hv] using kD.isLt⟩
  refine ⟨j,ko,q,ho,kC,?_⟩
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D) f kD.val=p := by simpa only [hf] using hp
  simpa [f,kC] using (pp ring hL f kD.val).symm.trans h0
private theorem self (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i (raw (C i)).label.val=i := by
  have ml (a b : Nat) : (a%n+b)%n=(a+b)%n := by
    rw [Nat.add_mod (a%n) b n,Nat.mod_mod]; exact (Nat.add_mod a b n).symm
  have mr (a b : Nat) : (a+b%n)%n=(a+b)%n := by
    rw [Nat.add_mod a (b%n) n,Nat.mod_mod]; exact (Nat.add_mod a b n).symm
  let L := (raw (C i)).label.val
  apply Fin.ext; change ((((i.val+n-(L%n))%n)+L)%n)=i.val
  rw [ml (i.val+n-(L%n)) L,←mr (i.val+n-(L%n)) L]
  have hm : L%n≤i.val+n := by have := Nat.mod_lt L ring.hn; omega
  rw [Nat.sub_add_cancel hm,Nat.add_mod,Nat.mod_eq_of_lt i.isLt,
    Nat.mod_self,Nat.add_zero,Nat.mod_eq_of_lt i.isLt]
private theorem clearMC (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) m t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3,setControl,clearMain,R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier,R2Coherence.raw]
private theorem p8_of_p9 (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : SweepOpenROverlapFreshWideV31 ring C) : SweepOpenROverlapFreshV31 ring C := by
  intro e o hs hp; have x:=h e o hs hp; refine ⟨?_,x.1⟩
  let d : Fin (ψ-(raw (C e)).label.val) := ⟨0,Nat.sub_pos_of_lt (raw (C e)).label.isLt⟩
  have z:=x.2 d
  have hz : R2Coherence.fwd ring e 0=e := by apply Fin.ext; simp [R2Coherence.fwd,Nat.mod_eq_of_lt e.isLt]
  simpa [d,hz] using z

private theorem ownerFreshDelete (ring : DirectedRing n) {C D : FC n ψ κ τ} (o : Fin n)
    (hL : ∀p,(raw (D p)).label=(raw (C p)).label)
    (hCell : ∀p,raw (D p)=raw (C p) ∨
      ((FreshnessClearV31 (C p)∧(raw (D p)).state≠.equal)∨
        ¬InOpenRFreshFootprintV31 ring C o p))
    (h : OpenROwnerFreshV3 ring C o) : OpenROwnerFreshV3 ring D o := by
  have rawE (u : Cell ψ κ τ) : R2Coherence.raw (eraseCellV3 u)=raw u := rfl
  unfold OpenROwnerFreshV3 at h ⊢; intro j ko hit; rw [gp ring hL j ko.val] at hit
  have hg:=h j ko hit; unfold GroupIntrinsicFreshV3 at hg ⊢; intro q
  rw [gp ring hL j q.val]; let f:=R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D f
  have old : IntrinsicFreshAtV3 ring C f := by simpa [f] using hg q
  unfold IntrinsicFreshAtV3 at old ⊢; intro heq
  rcases hCell f with hs|hc
  · have ec : (raw (C f)).state=.equal := by rw [←hs]; exact heq
    have ha:=old ec; intro kD
    have hv:=congrArg Fin.val (hL f)
    let kC : Fin ((raw (C f)).label.val+1):=⟨kD.val,by simpa only [hv] using kD.isLt⟩
    have hk:=ha kC; rw [pp ring hL f kD.val]
    let p:=R2Coherence.prefixPos ring (eraseCfgV3 C) f kD.val
    change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
    have hk' : R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by simpa [p,kC] using hk
    rcases hCell p with hp|hp
    · unfold R2Coherence.freshComponent at hk' ⊢
      rw [rawE (D p),hp]; rw [rawE (C p)] at hk'; exact hk'
    · rcases hp with hp|hout
      · exact (freshComponent_false_of_freshnessClear (C p) kD.val hp.1 hk').elim
      · exfalso; apply hout; refine ⟨j,ko,q,hit,kC,?_⟩; simpa [f,p,kC]
  · rcases hc with hc|hout
    · exact (hc.2 heq).elim
    · exfalso; apply hout
      let k : Fin ((raw (C f)).label.val+1):=⟨(raw (C f)).label.val,Nat.lt_succ_self _⟩
      refine ⟨j,ko,q,hit,k,?_⟩; apply Fin.ext
      simp [f,k,R2Coherence.prefixPos,R2Coherence.back,Nat.add_mod,
        Nat.mod_eq_of_lt f.isLt,ring.hn]

private theorem tailsFrame (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀p,(raw (D p)).label=(raw (C p)).label)
    (hTok : ∀p t,t≠.none→t≠.commit→t≠.release→(D p).ctl.tok=t→(C p).ctl.tok=t)
    (hFC : ∀p,FreshnessClearV31 (C p)→FreshnessClearV31 (D p))
    (hOF : ∀o,OpenROwnerFreshV3 ring C o→OpenROwnerFreshV3 ring D o)
    (h7 : ScrubLIncomingOpenRFreshV31 ring C) (h9 : SweepOpenROverlapFreshWideV31 ring C)
    (hS : SeekIncomingSweepOpenROverlapFreshWideV31 ring C)
    (h1 : OpenRForwardFreshnessClearV31 ring C) :
    ScrubLIncomingOpenRFreshV31 ring D ∧ SweepOpenROverlapFreshV31 ring D ∧
    SweepOpenROverlapFreshWideV31 ring D ∧ SeekIncomingSweepOpenROverlapFreshWideV31 ring D ∧
    OpenRForwardFreshnessClearV31 ring D := by
  have pend : ∀o,PendingOpenROwnerV31 ring D o→PendingOpenROwnerV31 ring C o := by
    intro o x; rcases x with ⟨hs,hu,hr⟩
    refine ⟨hTok _ .scrubL (by decide) (by decide) (by decide) hs,?_,?_⟩
    · unfold successorB at hu ⊢; simpa [hL o,hL (ring.rightNeighbor o)] using hu
    · unfold atRootB at hr ⊢; simpa [hL o] using hr
  have safe : ∀o p,SweepOpenRSafeFreshV31 ring C o p→SweepOpenRSafeFreshV31 ring D o p := by
    intro o p x; rcases x with x|x
    · exact Or.inl (hFC p x)
    · exact Or.inr (fun hd=>x (foot ring hL o p hd))
  have w : SweepOpenROverlapFreshWideV31 ring D := by
    intro s o hs hp; have x:=h9 s o (hTok _ .sweep (by decide) (by decide) (by decide) hs) (pend o hp)
    refine ⟨safe o _ x.1,?_⟩; intro d
    have hv:=congrArg Fin.val (hL s); let dc : Fin (ψ-(raw (C s)).label.val):=⟨d.val,by simpa only [hv] using d.isLt⟩
    exact safe o _ (by simpa [dc] using x.2 dc)
  have s : SeekIncomingSweepOpenROverlapFreshWideV31 ring D := by
    intro a o hk hp; have x:=hS a o (hTok _ .seek (by decide) (by decide) (by decide) hk) (pend o hp)
    constructor
    · intro hr; have z : atRootB (C (ring.rightNeighbor a))=true := by unfold atRootB at hr ⊢; simpa [hL _] using hr
      rcases x.1 z with ⟨u,v⟩; exact ⟨safe o _ u,fun d=>safe o _ (v ⟨d.val,by simpa only [congrArg Fin.val (hL _)] using d.isLt⟩)⟩
    · intro hn hr; have zn : atRootB (C (ring.rightNeighbor a))=false := by unfold atRootB at hn ⊢; simpa [hL _] using hn
      have zr : atRootB (C a)=true := by unfold atRootB at hr ⊢; simpa [hL _] using hr
      rcases x.2 zn zr with ⟨u,v⟩; exact ⟨safe o _ u,fun d=>safe o _ (v ⟨d.val,by simpa only [congrArg Fin.val (hL _)] using d.isLt⟩)⟩
  have r1 : OpenRForwardFreshnessClearV31 ring D := by
    intro o ho d; have oc:=hTok o .openR (by decide) (by decide) (by decide) ho
    have hv:=congrArg Fin.val (hL o); let dc : Fin (ψ-(raw (C o)).label.val):=⟨d.val,by simpa only [hv] using d.isLt⟩
    exact hFC _ (by simpa [dc] using h1 o oc dc)
  refine ⟨?_,p8_of_p9 ring D w,w,s,r1⟩
  intro o hs hu hr; exact hOF o (h7 o (hTok _ .scrubL (by decide) (by decide) (by decide) hs)
    (by unfold successorB at hu ⊢; simpa [hL o,hL (ring.rightNeighbor o)] using hu)
    (by unfold atRootB at hr ⊢; simpa [hL o] using hr))

theorem commitStep_reachable_fresh
    (hψ : 0<ψ) (h2 : 2≤ψ) (ring : DirectedRing n) :
    StepPreservesV31_commit_fresh (κ:=κ) (τ:=τ) hψ h2 ring := by
  intro C e hGeom _ hF hb
  rcases hF with ⟨hFacts,h7,_h8,h9,hS,h1,hR2⟩
  let D := stepV3 hψ h2 ring C e
  let r := ring.rightNeighbor e
  have hc : (C e).ctl.tok≠.sweep ∧ (C r).ctl.tok=.commit := by
    unfold branchAtV3 at hb
    repeat' split at hb <;> simp_all [r] <;> grind
  have le : D e=(commitStageV3 (C e) (C r)).1 := by
    dsimp [D]
    simp [stepV3,protocolV3,PopulationProtocol.step,rowV3,r,hc.1,hc.2]
  have re (hne:r≠e) : D r=setControl (clearMain (C r)) .sealed .none := by
    dsimp [D]
    simp [stepV3,protocolV3,PopulationProtocol.step,rowV3,r,hc.1,hc.2,
      hne,commitStageV3]
  have hL : ∀p,(raw (D p)).label=(raw (C p)).label := fun p=>by
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hcr : MainClearV3 (C r) := by
    have x:=hFacts.2.1 r hc.2 (raw (C r)).label
    dsimp only at x
    rw [self ring C r] at x
    exact x.1
  have startEq (hz:atRootB (C r)=false) :
      R2Coherence.groupStart ring (eraseCfgV3 C) r =
        R2Coherence.groupStart ring (eraseCfgV3 C) e := by
    have hs:=hGeom e
    unfold passiveEdgeOKV3 at hs
    have hv:(raw (C r)).label.val=(raw (C e)).label.val+1 := by
      simpa [r,hz,successorB] using hs
    unfold R2Coherence.groupStart
    change R2Coherence.back ring r (raw (C r)).label.val =
      R2Coherence.back ring e (raw (C e)).label.val
    rw [hv]
    simpa [r] using
      R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
        ring e (raw (C e)).label.val
  have hce : atRootB (C r)=false→MainClearV3 (C e) := by
    intro hz
    have x:=hFacts.2.1 r hc.2 (raw (C e)).label
    dsimp only at x
    have z:R2Coherence.groupPos ring (eraseCfgV3 C) r
        (raw (C e)).label.val=e := by
      unfold R2Coherence.groupPos
      rw [startEq hz]
      exact self ring C e
    rw [z] at x
    exact x.1
  have frame : ∀p,D p=C p ∨ (MainClearV3 (D p)∧PhaseOwnedV31 (D p)) := by
    intro p
    by_cases pe:p=e
    · subst p
      rw [le]
      unfold commitStageV3
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr ⟨clearMC _ .sealed .none,
            by simp [PhaseOwnedV31,setControl]⟩
        · exact Or.inr ⟨clearMC _ .closing .commit,
            by simp [PhaseOwnedV31,setControl]⟩
    · by_cases pr:p=r
      · subst p
        rw [re pe]
        exact Or.inr ⟨clearMC _ .sealed .none,
          by simp [PhaseOwnedV31,setControl]⟩
      · exact Or.inl (by
          dsimp [D]
          exact stepV3_other hψ h2 ring C e p pe pr)
  have mono : ∀p,MainClearV3 (C p)∧PhaseOwnedV31 (C p)→
      MainClearV3 (D p)∧PhaseOwnedV31 (D p) := by
    intro p x
    rcases frame p with z|z
    · simpa [z] using x
    · exact z
  have sameTok : ∀p t,t≠.none→t≠.commit→(D p).ctl.tok=t→D p=C p := by
    intro p t hn hk ht
    by_cases pe:p=e
    · subst p
      rw [le] at ht ⊢
      by_cases hrr:atRootB (C r)=true
      · simp [commitStageV3,hrr]
      · have hrf:atRootB (C r)=false := by
          cases q:atRootB (C r) <;> simp_all
        by_cases hl:atRootB (C e)=true
        · exfalso
          apply hn
          simpa [commitStageV3,hrf,hl,setControl] using ht.symm
        · have hlf:atRootB (C e)=false := by
            cases q:atRootB (C e) <;> simp_all
          exfalso
          apply hk
          simpa [commitStageV3,hrf,hlf,setControl] using ht.symm
    · by_cases pr:p=r
      · subst p
        rw [re pe] at ht
        exfalso
        apply hn
        simpa [setControl] using ht.symm
      · dsimp [D]
        exact stepV3_other hψ h2 ring C e p pe pr
  have cell : ∀p,D p=C p ∨ MainClearV3 (C p) := by
    intro p
    by_cases pe:p=e
    · subst p
      by_cases hz:atRootB (C r)=true
      · exact Or.inl (by rw [le]; simp [commitStageV3,hz])
      · have hzf:atRootB (C r)=false := by
          cases q:atRootB (C r) <;> simp_all
        exact Or.inr (hce hzf)
    · by_cases pr:p=r
      · subst p
        exact Or.inr hcr
      · exact Or.inl (by
          dsimp [D]
          exact stepV3_other hψ h2 ring C e p pe pr)
  have hMC : ∀p,MainClearV3 (C p)→MainClearV3 (D p) := by
    intro p x
    rcases frame p with z|z
    · simpa [z] using x
    · exact z.1
  have hCell : ∀o p,raw (D p)=raw (C p) ∨
      ((FreshnessClearV31 (C p)∧(raw (D p)).state≠.equal)∨
        ¬InOpenRFreshFootprintV31 ring C o p) := by
    intro o p
    rcases cell p with z|z
    · exact Or.inl (congrArg raw z)
    · refine Or.inr (Or.inl ⟨freshnessClear_of_mainClear _ z,?_⟩)
      have hm:=hMC p z
      unfold MainClearV3 R2CoherenceBranches.MainClear at hm
      have hn:(raw (D p)).state=.none := by
        simpa [raw,eraseCellV3,R2Coherence.raw] using hm.1
      intro heq
      rw [hn] at heq
      cases heq
  have hOF : ∀o,OpenROwnerFreshV3 ring C o→OpenROwnerFreshV3 ring D o :=
    fun o=>ownerFreshDelete ring o hL (hCell o)
  have hFC : ∀p,FreshnessClearV31 (C p)→FreshnessClearV31 (D p) := by
    intro p x
    rcases frame p with z|z
    · simpa [z] using x
    · exact freshnessClear_of_mainClear _ z.1
  have gT : ∀i,GroupOwnedClearV31 ring C i→GroupOwnedClearV31 ring D i := by
    intro i x k
    rw [gp ring hL i k.val]
    exact mono _ (x k)
  have sT : ∀i,SweptPrefixOwnedClearV31 ring C i→
      SweptPrefixOwnedClearV31 ring D i := by
    intro i x kD
    have hv:=congrArg Fin.val (hL i)
    let kC:Fin (raw (C i)).label.val:=
      ⟨kD.val,by simpa only [hv] using kD.isLt⟩
    rw [gp ring hL i kD.val]
    exact mono _ (by simpa [kC] using x kC)
  have reidx (a b:Fin n)
      (hs:R2Coherence.groupStart ring (eraseCfgV3 C) a=
        R2Coherence.groupStart ring (eraseCfgV3 C) b)
      (x:GroupOwnedClearV31 ring C b) : GroupOwnedClearV31 ring C a := by
    intro k
    have z:R2Coherence.groupPos ring (eraseCfgV3 C) a k.val=
        R2Coherence.groupPos ring (eraseCfgV3 C) b k.val := by
      unfold R2Coherence.groupPos
      rw [hs]
    rw [z]
    exact x k
  have hFD : ReachablePhaseFactsV31 ring D := by
    rcases hFacts with ⟨a,b,c,d,f,g⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i hi
      have z:=sameTok i .sweep (by decide) (by decide) hi
      rw [z] at hi
      exact sT i (a i hi)
    · intro i hi
      by_cases ie:i=e
      · subst i
        by_cases hz:atRootB (C r)=true
        · have q:=hi
          rw [le] at q
          exact gT e (b e (by simpa [commitStageV3,hz] using q))
        · have hzf:atRootB (C r)=false := by
            cases q:atRootB (C r) <;> simp_all
          by_cases hl:atRootB (C e)=true
          · rw [le] at hi
            simp [commitStageV3,hzf,hl,setControl] at hi
          · exact gT e (reidx e r (startEq hzf).symm (b r hc.2))
      · by_cases ir:i=r
        · subst i
          rw [re ie] at hi
          simp [setControl] at hi
        · have z:D i=C i := by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e i ie ir
          rw [z] at hi
          exact gT i (b i hi)
    · intro i hi
      by_cases ie:i=e
      · subst i
        by_cases hz:atRootB (C r)=true
        · have q:=hi
          rw [le] at q
          exact gT e (c e (by simpa [commitStageV3,hz] using q))
        · have hzf:atRootB (C r)=false := by
            cases q:atRootB (C r) <;> simp_all
          by_cases hl:atRootB (C e)=true
          · exact gT e (reidx e r (startEq hzf).symm (b r hc.2))
          · have hlf:atRootB (C e)=false := by
              cases q:atRootB (C e) <;> simp_all
            rw [le] at hi
            simp [commitStageV3,hzf,hlf,setControl] at hi
      · by_cases ir:i=r
        · subst i
          exact gT r (b r hc.2)
        · have z:D i=C i := by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e i ie ir
          rw [z] at hi
          exact gT i (c i hi)
    · intro i hi
      have z:=sameTok i .release (by decide) (by decide) hi
      rw [z] at hi
      rcases d i hi with ⟨m,q⟩
      exact ⟨by rw [z]; exact m,gT i q⟩
    · intro i hi
      have z:=sameTok i .scrubL (by decide) (by decide) hi
      rw [z] at hi
      rcases f i hi with ⟨m,nz,q⟩
      exact ⟨by rw [z]; exact m,by rw [z]; exact nz,gT i q⟩
    · intro i hi
      have z:=sameTok i .openR (by decide) (by decide) hi
      rw [z] at hi
      rcases g i hi with ⟨m,q⟩
      exact ⟨by rw [z]; exact m,hOF i q⟩
  have T:=tailsFrame ring hL
    (fun p t hn hk _ ht=>by
      have z:=sameTok p t hn hk ht
      rw [z] at ht
      exact ht) hFC hOF h7 h9 hS h1
  have r2 : SweepPendingOpenRFootprintOwnedV31F ring D := by
    intro s o p hs hp hr0 hf
    have zs:=sameTok s .sweep (by decide) (by decide) hs
    rw [zs] at hs
    rcases hp with ⟨ha,hu,hro⟩
    have zo:=sameTok (ring.rightNeighbor o) .scrubL
      (by decide) (by decide) ha
    rw [zo] at ha
    have hpC:PendingOpenROwnerV31 ring C o :=
      ⟨ha,
       (by unfold successorB at hu ⊢
           simpa [hL o,hL (ring.rightNeighbor o)] using hu),
       (by unfold atRootB at hro ⊢; simpa [hL o] using hro)⟩
    have hrC:InSweepWideReadV31 ring C s p := by
      rcases hr0 with z|⟨d0,hd⟩
      · exact Or.inl z
      · right
        have hv:=congrArg Fin.val (hL s)
        exact ⟨⟨d0.val,by simpa only [hv] using d0.isLt⟩,hd⟩
    rcases hR2 s o p hs hpC hrC (foot ring hL o p hf) with x|x
    · left
      rcases frame p with z|z
      · rw [z]
        exact x
      · exact z.2
    · exact Or.inr (hFC p x)
  exact ⟨hFD,T.1,T.2.1,T.2.2.1,T.2.2.2.1,T.2.2.2.2,r2⟩

theorem sealedStep_reachable_fresh
    (hψ : 0<ψ) (h2 : 2≤ψ) (ring : DirectedRing n) :
    StepPreservesV31_sealed_fresh (κ:=κ) (τ:=τ) hψ h2 ring := by
  intro C e _ _ hF hb
  rcases hF with ⟨hFacts,h7,_h8,h9,hS,h1,hR2⟩
  let D:=stepV3 hψ h2 ring C e
  let r:=ring.rightNeighbor e
  have hc : (C e).ctl.tok=.none∧(C r).ctl.tok=.none∧
      (C e).ctl.mark=.sealed∧(C r).ctl.mark=.sealed := by
    unfold branchAtV3 at hb
    repeat' split at hb <;> simp_all [r] <;> grind
  have le : D e=(sealedStageV3 hψ (by decide:0<2) h2 (C e) (C r)).1 := by
    dsimp [D]
    simp [stepV3,protocolV3,PopulationProtocol.step,rowV3,ordinaryStageV3,
      r,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  have re (hne:r≠e) :
      D r=(sealedStageV3 hψ (by decide:0<2) h2 (C e) (C r)).2 := by
    dsimp [D]
    simp [stepV3,protocolV3,PopulationProtocol.step,rowV3,ordinaryStageV3,
      r,hne,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  have hce : MainClearV3 (C e) := by
    have x:=hFacts.2.2.1 e hc.2.2.1 (raw (C e)).label
    dsimp only at x
    rw [self ring C e] at x
    exact x.1
  have hcr : MainClearV3 (C r) := by
    have x:=hFacts.2.2.1 r hc.2.2.2 (raw (C r)).label
    dsimp only at x
    rw [self ring C r] at x
    exact x.1
  have hL : ∀p,(raw (D p)).label=(raw (C p)).label := fun p=>by
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hCtl : ∀p,(D p).ctl=(C p).ctl∨
      (p=e∧(D p).ctl=⟨.releasing,.release⟩) := by
    intro p
    by_cases pe:p=e
    · subst p
      rw [le]
      unfold sealedStageV3
      split
      · right
        simp [setControl]
      · left
        dsimp only
        split <;> simp [install]
    · by_cases pr:p=r
      · subst p
        left
        rw [re pe]
        unfold sealedStageV3
        split
        · rfl
        · dsimp only
          split <;> simp [install]
      · left
        exact congrArg Cell.ctl (by
          dsimp [D]
          exact stepV3_other hψ h2 ring C e p pe pr)
  have mcSet (u:Cell ψ κ τ) m t :
      MainClearV3 (setControl u m t)↔MainClearV3 u := by
    simp [MainClearV3,R2CoherenceBranches.MainClear,eraseCellV3,
      setControl,R2Coherence.raw]
  have mcI (u:Cell ψ κ τ) (q:R2.Cell ψ κ τ) :
      MainClearV3 (install u (R2Coherence.clearMainPhys q)) := by
    unfold MainClearV3 R2CoherenceBranches.MainClear
    simp [install,eraseCellV3,R2Coherence.clearMainPhys,
      PPLLExpiringComparisonRepair.clearComparisonCarrier,R2Coherence.raw]
  have hMC : ∀p,MainClearV3 (C p)→MainClearV3 (D p) := by
    intro p hm
    by_cases pe:p=e
    · subst p
      rw [le]
      unfold sealedStageV3
      split
      · exact (mcSet _ _ _).2 hce
      · dsimp only
        split
        · exact hce
        · exact mcI _ _
    · by_cases pr:p=r
      · subst p
        rw [re pe]
        unfold sealedStageV3
        split
        · exact hcr
        · dsimp only
          split
          · exact hcr
          · exact mcI _ _
      · rw [show D p=C p by
          dsimp [D]
          exact stepV3_other hψ h2 ring C e p pe pr]
        exact hm
  have hPO : ∀p,PhaseOwnedV31 (C p)→PhaseOwnedV31 (D p) := by
    intro p x
    rcases hCtl p with z|⟨_,z⟩
    · unfold PhaseOwnedV31 at x ⊢
      rw [z]
      exact x
    · simpa [PhaseOwnedV31,z]
  have mono : ∀p,MainClearV3 (C p)∧PhaseOwnedV31 (C p)→
      MainClearV3 (D p)∧PhaseOwnedV31 (D p) :=
    fun p x=>⟨hMC p x.1,hPO p x.2⟩
  have oldCtl : ∀p {t:TokenV3},t≠.release→(D p).ctl.tok=t→
      (D p).ctl=(C p).ctl := by
    intro p t hn ht
    rcases hCtl p with z|⟨_,z⟩
    · exact z
    · exfalso
      apply hn
      have q:=ht
      rw [z] at q
      exact q.symm
  have tok : ∀p t,t≠.release→(D p).ctl.tok=t→(C p).ctl.tok=t := by
    intro p t hn ht
    have z:=oldCtl p hn ht
    rw [z] at ht
    exact ht
  have mark : ∀p,(D p).ctl.mark=.sealed→(C p).ctl.mark=.sealed := by
    intro p hm
    rcases hCtl p with z|⟨_,z⟩
    · rw [z] at hm
      exact hm
    · have q:=hm
      rw [z] at q
      cases q
  have cell : ∀p,D p=C p∨MainClearV3 (C p) := by
    intro p
    by_cases pe:p=e
    · exact Or.inr (by simpa [pe] using hce)
    · by_cases pr:p=r
      · exact Or.inr (by simpa [pr] using hcr)
      · exact Or.inl (by
          dsimp [D]
          exact stepV3_other hψ h2 ring C e p pe pr)
  have hCell : ∀o p,raw (D p)=raw (C p)∨
      ((FreshnessClearV31 (C p)∧(raw (D p)).state≠.equal)∨
        ¬InOpenRFreshFootprintV31 ring C o p) := by
    intro o p
    rcases cell p with z|z
    · exact Or.inl (congrArg raw z)
    · refine Or.inr (Or.inl ⟨freshnessClear_of_mainClear _ z,?_⟩)
      have hm:=hMC p z
      unfold MainClearV3 R2CoherenceBranches.MainClear at hm
      have hn:(raw (D p)).state=.none := by
        simpa [raw,eraseCellV3,R2Coherence.raw] using hm.1
      intro heq
      rw [hn] at heq
      cases heq
  have hOF : ∀o,OpenROwnerFreshV3 ring C o→OpenROwnerFreshV3 ring D o :=
    fun o=>ownerFreshDelete ring o hL (hCell o)
  have hFC : ∀p,FreshnessClearV31 (C p)→FreshnessClearV31 (D p) := by
    intro p x
    rcases cell p with z|z
    · simpa [z] using x
    · exact freshnessClear_of_mainClear _ (hMC p z)
  have gT : ∀i,GroupOwnedClearV31 ring C i→GroupOwnedClearV31 ring D i := by
    intro i x k
    rw [gp ring hL i k.val]
    exact mono _ (x k)
  have sT : ∀i,SweptPrefixOwnedClearV31 ring C i→
      SweptPrefixOwnedClearV31 ring D i := by
    intro i x kD
    have hv:=congrArg Fin.val (hL i)
    let kC:Fin (raw (C i)).label.val:=
      ⟨kD.val,by simpa only [hv] using kD.isLt⟩
    rw [gp ring hL i kD.val]
    exact mono _ (by simpa [kC] using x kC)
  rcases hFacts with ⟨a,b,c,d,f,g⟩
  have hFD : ReachablePhaseFactsV31 ring D := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i hi
      exact sT i (a i (tok i .sweep (by decide) hi))
    · intro i hi
      exact gT i (b i (tok i .commit (by decide) hi))
    · intro i hi
      exact gT i (c i (mark i hi))
    · intro i hi
      rcases hCtl i with z|⟨ie,z⟩
      · have q:=d i (by rw [z] at hi; exact hi)
        exact ⟨by rw [z]; exact q.1,gT i q.2⟩
      · subst i
        exact ⟨by rw [z],gT e (c e hc.2.2.1)⟩
    · intro i hi
      have z:=oldCtl i (by decide) hi
      have hiC:(C i).ctl.tok=.scrubL := by
        rw [←z]
        exact hi
      have q:=f i hiC
      refine ⟨?_,?_,gT i q.2.2⟩
      · rw [z]
        exact q.1
      · intro hz
        apply q.2.1
        exact (congrArg Fin.val (hL i)).symm.trans hz
    · intro i hi
      have z:=oldCtl i (by decide) hi
      have hiC:(C i).ctl.tok=.openR := by
        rw [←z]
        exact hi
      have q:=g i hiC
      exact ⟨by rw [z]; exact q.1,hOF i q.2⟩
  have T:=tailsFrame ring hL
    (fun p t _ _ hn ht=>tok p t hn ht) hFC hOF h7 h9 hS h1
  have pend : ∀o,PendingOpenROwnerV31 ring D o→
      PendingOpenROwnerV31 ring C o := by
    intro o x
    rcases x with ⟨hs,hu,hr0⟩
    refine ⟨tok _ .scrubL (by decide) hs,?_,?_⟩
    · unfold successorB at hu ⊢
      simpa [hL o,hL (ring.rightNeighbor o)] using hu
    · unfold atRootB at hr0 ⊢
      simpa [hL o] using hr0
  have r2 : SweepPendingOpenRFootprintOwnedV31F ring D := by
    intro s o p hs hp rd ff
    have hsC:=tok s .sweep (by decide) hs
    have hpC:=pend o hp
    have rdC:InSweepWideReadV31 ring C s p := by
      rcases rd with z|⟨d0,hd⟩
      · exact Or.inl z
      · right
        have hv:=congrArg Fin.val (hL s)
        exact ⟨⟨d0.val,by simpa only [hv] using d0.isLt⟩,hd⟩
    rcases hR2 s o p hsC hpC rdC (foot ring hL o p ff) with x|x
    · exact Or.inl (hPO p x)
    · exact Or.inr (hFC p x)
  exact ⟨hFD,T.1,T.2.1,T.2.2.1,T.2.2.2.1,T.2.2.2.2,r2⟩

/-- Fresh restatement of Sweep3's served-safety residual. -/
def SweepCurrentOpenRServedSafeFreshV31
    (hψ : 0<ψ) (h2 : 2≤ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C:FC n ψ κ τ) (e o:Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C → ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e))=.sweep → (C o).ctl.tok=.openR →
      SweepOpenRSafeFreshV31 ring C o e ∧ SweepOpenRSafeFreshV31 ring C o (ring.rightNeighbor e)
/-- Fresh restatement of Sweep2's post-tail residual. -/
def SweepStrongTailPreservationFreshV31
    (hψ : 0<ψ) (h2 : 2≤ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C:FC n ψ κ τ) (e:Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C → ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e))=.sweep →
      SeekIncomingSweepOpenROverlapFreshWideV31 ring (stepV3 hψ h2 ring C e) ∧
      OpenRForwardFreshnessClearV31 ring (stepV3 hψ h2 ring C e) ∧
      R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F ring (stepV3 hψ h2 ring C e)

theorem sweepStep_reachable_fresh_of_residuals
    (hψ : 0<ψ) (h2 : 2≤ψ) (ring : DirectedRing n)
    (hSafe : SweepCurrentOpenRServedSafeFreshV31 (κ:=κ) (τ:=τ) hψ h2 ring)
    (hTail : SweepStrongTailPreservationFreshV31 (κ:=κ) (τ:=τ) hψ h2 ring) :
    StepPreservesV31_sweep_fresh (κ:=κ) (τ:=τ) hψ h2 ring := by
  intro C e hGeom hTrace hF hb
  have hFresh : ReachablePhaseFactsFreshV31 ring C := hF
  rcases hF with ⟨hFacts,h7,_h8,h9,_hS,_h1,_hR2⟩
  let D:=stepV3 hψ h2 ring C e
  let r:=ring.rightNeighbor e
  have bc : (C r).ctl.tok≠.seek∧(C e).ctl.tok=.sweep := by
    unfold branchAtV3 at hb
    repeat' split at hb <;> simp_all [r] <;> grind
  have le : D e=(sweepStageV3 (C e) (C r)).1 := by
    dsimp [D]
    simp [stepV3,protocolV3,PopulationProtocol.step,rowV3,r,bc.1,bc.2]
  have re (hne:r≠e) : D r=(sweepStageV3 (C e) (C r)).2 := by
    dsimp [D]
    simp [stepV3,protocolV3,PopulationProtocol.step,rowV3,r,bc.1,bc.2,hne]
  have hL : ∀p,(raw (D p)).label=(raw (C p)).label := fun p=>by
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have bf (b:Bool) (h:b≠true) : b=false := by cases b <;> simp_all
  have old : ∀p {t:TokenV3},t≠.none→t≠.seek→t≠.sweep→t≠.commit→
      (D p).ctl.tok=t→D p=C p := by
    intro p t h0 hk hw hc ht
    by_cases pe:p=e
    · subst p
      rw [le] at ht ⊢
      by_cases st:successorB (C e) (C r)=true
      · exfalso
        apply h0
        simpa [sweepStageV3,st,setControl] using ht.symm
      · have sf:=bf _ st
        exfalso
        apply hk
        simpa [sweepStageV3,sf,startClosing,setControl] using ht.symm
    · by_cases pr:p=r
      · subst p
        rw [re pe] at ht ⊢
        by_cases st:successorB (C e) (C r)=true
        · by_cases q:atTerminalB (C r)=true
          · exfalso
            apply hc
            simpa [sweepStageV3,st,q,setControl] using ht.symm
          · have qf:=bf _ q
            exfalso
            apply hw
            simpa [sweepStageV3,st,qf,setControl] using ht.symm
        · have sf:=bf _ st
          simp [sweepStageV3,sf]
      · dsimp [D]
        exact stepV3_other hψ h2 ring C e p pe pr
  have hFC : ∀p,FreshnessClearV31 (C p)→FreshnessClearV31 (D p) := by
    intro p hf
    by_cases st:successorB (C e) (C r)=true
    · by_cases pe:p=e
      · subst p
        rw [le]
        simp [sweepStageV3,st]
        exact freshnessClear_of_mainClear _ (clearMC _ .closing .none)
      · by_cases pr:p=r
        · subst p
          rw [re pe]
          simp [sweepStageV3,st]
          exact freshnessClear_of_mainClear _ (clearMC _ .closing _)
        · rw [show D p=C p by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e p pe pr]
          exact hf
    · have sf:=bf _ st
      unfold FreshnessClearV31 at hf ⊢
      by_cases pe:p=e
      · subst p
        rw [le]
        simpa [sweepStageV3,sf,startClosing,setControl,raw] using hf
      · by_cases pr:p=r
        · subst p
          rw [re pe]
          simpa [sweepStageV3,sf] using hf
        · rw [show D p=C p by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e p pe pr]
          exact hf
  have owner (o:Fin n)
      (sa:SweepOpenRSafeFreshV31 ring C o e∧SweepOpenRSafeFreshV31 ring C o r)
      (hf:OpenROwnerFreshV3 ring C o) : OpenROwnerFreshV3 ring D o := by
    refine ownerFreshDelete ring o hL ?_ hf
    intro p
    by_cases st:successorB (C e) (C r)=true
    · by_cases pe:p=e
      · subst p
        rcases sa.1 with z|z
        · refine Or.inr (Or.inl ⟨z,?_⟩)
          rw [le]
          simp [sweepStageV3,st,setControl,clearMain,raw]
        · exact Or.inr (Or.inr z)
      · by_cases pr:p=r
        · subst p
          rcases sa.2 with z|z
          · refine Or.inr (Or.inl ⟨z,?_⟩)
            rw [re pe]
            simp [sweepStageV3,st,setControl,clearMain,raw]
          · exact Or.inr (Or.inr z)
        · exact Or.inl (congrArg raw (by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e p pe pr))
    · have sf:=bf _ st
      by_cases pe:p=e
      · subst p
        left
        rw [le]
        simp [sweepStageV3,sf,startClosing,setControl,raw]
      · by_cases pr:p=r
        · subst p
          left
          rw [re pe]
          simp [sweepStageV3,sf,raw]
        · exact Or.inl (congrArg raw (by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e p pe pr))
  have pend : ∀o,PendingOpenROwnerV31 ring D o→PendingOpenROwnerV31 ring C o := by
    intro o x
    rcases x with ⟨hs,hu,hr0⟩
    have z:=old (ring.rightNeighbor o) (t:=.scrubL)
      (by decide) (by decide) (by decide) (by decide) hs
    rw [z] at hs
    refine ⟨hs,?_,?_⟩
    · unfold successorB at hu ⊢
      simpa [hL o,hL (ring.rightNeighbor o)] using hu
    · unfold atRootB at hr0 ⊢
      simpa [hL o] using hr0
  have hP6 : ∀o,(D o).ctl.tok=.openR→
      (D o).ctl.mark=.releasing∧OpenROwnerFreshV3 ring D o := by
    intro o ho
    have z:=old o (t:=.openR) (by decide) (by decide) (by decide) (by decide) ho
    have oc:(C o).ctl.tok=.openR := by rw [z] at ho; exact ho
    have q:=hFacts.2.2.2.2.2 o oc
    have sa:=hSafe C e o hGeom hTrace hFresh hb oc
    exact ⟨by rw [z]; exact q.1,owner o (by simpa [r] using sa) q.2⟩
  -- END PART 1

  have ph:=R2CoherenceV31ReachableSweep.sweepStep_reachable_phase
    hψ h2 ring C e hTrace hFacts hb
  have hFD : ReachablePhaseFactsV31 ring D := by
    refine ⟨ph.1,ph.2.1,ph.2.2.1,?_,?_,hP6⟩
    · intro i hi
      have z:=old i (t:=.release) (by decide) (by decide) (by decide) (by decide) hi
      have hiC:(C i).ctl.tok=.release := by rw [z] at hi; exact hi
      have q:=hFacts.2.2.2.1 i hiC
      exact ⟨by rw [z]; exact q.1,ph.2.2.2.1 i hi⟩
    · intro i hi
      have z:=old i (t:=.scrubL) (by decide) (by decide) (by decide) (by decide) hi
      have hiC:(C i).ctl.tok=.scrubL := by rw [z] at hi; exact hi
      have q:=hFacts.2.2.2.2.1 i hiC
      exact ⟨by rw [z]; exact q.1,by rw [z]; exact q.2.1,
        ph.2.2.2.2 i hi⟩
  have h7D : ScrubLIncomingOpenRFreshV31 ring D := by
    intro o hs hu hr0
    have hp:=pend o ⟨hs,hu,hr0⟩
    have sa:=p8_of_p9 ring C h9 e o bc.2 hp
    exact owner o (by simpa [r] using sa) (h7 o hp.1 hp.2.1 hp.2.2)
  have safe : ∀o p,SweepOpenRSafeFreshV31 ring C o p→
      SweepOpenRSafeFreshV31 ring D o p := by
    intro o p x
    rcases x with x|x
    · exact Or.inl (hFC p x)
    · exact Or.inr (fun q=>x (foot ring hL o p q))
  have fwdR (i:Fin n) (d:Nat) :
      R2Coherence.fwd ring (ring.rightNeighbor i) d=
        R2Coherence.fwd ring i (d+1) := by
    apply Fin.ext
    unfold R2Coherence.fwd DirectedRing.rightNeighbor
    dsimp only
    rw [show (((i.val+1)%n)+d)%n=(i.val+1+d)%n by
      rw [Nat.add_mod]
      simp only [Nat.mod_mod]
      exact (Nat.add_mod _ _ _).symm]
    congr 1
    omega
  have h9D : SweepOpenROverlapFreshWideV31 ring D := by
    intro s o hs hp
    have hpC:=pend o hp
    by_cases st:successorB (C e) (C r)=true
    · have se:s≠e := by
        intro q
        subst s
        rw [le] at hs
        simp [sweepStageV3,st,setControl] at hs
      by_cases sr:s=r
      · subst s
        have tf:atTerminalB (C r)=false := by
          by_cases q:atTerminalB (C r)=true
          · rw [re se] at hs
            simp [sweepStageV3,st,q,setControl] at hs
          · exact bf _ q
        have src:=h9 e o bc.2 hpC
        have sl:(raw (C r)).label.val=(raw (C e)).label.val+1 := by
          simpa [successorB] using st
        have le0:(raw (C r)).label.val+1≤ψ :=
          Nat.succ_le_of_lt (raw (C r)).label.isLt
        have ne:(raw (C r)).label.val+1≠ψ := by
          intro heq
          have tt:atTerminalB (C r)=true := by simp [atTerminalB,heq]
          rw [tf] at tt
          cases tt
        have lt:(raw (C r)).label.val+1<ψ := by omega
        constructor
        · let d:Fin (ψ-(raw (C e)).label.val):=⟨2,by omega⟩
          have z:SweepOpenRSafeFreshV31 ring C o
              (R2Coherence.fwd ring e 2) := by
            simpa [d] using src.2 d
          have mv:R2Coherence.fwd ring e 2=ring.rightNeighbor r := by
            calc
              R2Coherence.fwd ring e 2 = R2Coherence.fwd ring r 1 := by
                simpa [r] using (fwdR e 1).symm
              _ = ring.rightNeighbor r := rfl
          rw [mv] at z
          exact safe o _ z
        · intro d
          have hv:=congrArg Fin.val (hL r)
          have hdR:d.val<ψ-(raw (C r)).label.val := by
            simpa only [hv] using d.isLt
          let dc:Fin (ψ-(raw (C e)).label.val):=⟨d.val+1,by omega⟩
          have z:SweepOpenRSafeFreshV31 ring C o
              (R2Coherence.fwd ring e (d.val+1)) := by
            simpa [dc] using src.2 dc
          have sh:R2Coherence.fwd ring r d.val=
              R2Coherence.fwd ring e (d.val+1) := by
            simpa [r] using fwdR e d.val
          rw [←sh] at z
          exact safe o _ z
      · have eq:D s=C s := by
          dsimp [D]
          exact stepV3_other hψ h2 ring C e s se sr
        have sc:(C s).ctl.tok=.sweep := by rw [eq] at hs; exact hs
        have src:=h9 s o sc hpC
        refine ⟨safe o _ src.1,?_⟩
        intro d
        have hv:=congrArg Fin.val (hL s)
        let dc:Fin (ψ-(raw (C s)).label.val):=
          ⟨d.val,by simpa only [hv] using d.isLt⟩
        exact safe o _ (by simpa [dc] using src.2 dc)
    · have sf:=bf _ st
      have se:s≠e := by
        intro q
        subst s
        rw [le] at hs
        simp [sweepStageV3,sf,startClosing,setControl] at hs
      have eq:D s=C s := by
        by_cases sr:s=r
        · subst s
          rw [re se]
          simp [sweepStageV3,sf]
        · dsimp [D]
          exact stepV3_other hψ h2 ring C e s se sr
      have sc:(C s).ctl.tok=.sweep := by rw [eq] at hs; exact hs
      have src:=h9 s o sc hpC
      refine ⟨safe o _ src.1,?_⟩
      intro d
      have hv:=congrArg Fin.val (hL s)
      let dc:Fin (ψ-(raw (C s)).label.val):=
        ⟨d.val,by simpa only [hv] using d.isLt⟩
      exact safe o _ (by simpa [dc] using src.2 dc)
  have t:=hTail C e hGeom hTrace hFresh hb
  exact ⟨hFD,h7D,p8_of_p9 ring D h9D,h9D,t.1,t.2.1,t.2.2⟩
end R2CoherenceV31ReachableFreshBranches1
