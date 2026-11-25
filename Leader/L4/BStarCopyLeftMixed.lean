import Leader.L4.BStarCopyLeftPending

namespace L4.BStarCopyLeftMixed
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongPrep BStarLongCommandData
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftDeposit BStarCopyLeftInjectionMark
open BStarCopyLeftRetained BStarCopyLeftRetainedClassify BStarCopyLeftDataSweep
open BStarCopyLeftReleaseClass BStarCopyLeftReleaseOrder BStarCopyLeftPending BStarCopyDownstream
open BStarCopyFIFO BStarCopyFenceSaturation BStarCopyMarkedLedger
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarSeparatingRail BStarAcquireForwardTrace BStarSeparatorControl
open BStarResetMarkAdapter
open BStarCopyRightStrip (addr addr_next addr_inj)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

private theorem distinct_destination {n : Nat} (a : Fin n) {i seam : Nat}
    (I : i<seam) (N : seam≤n) (ordinary : 0<i ∨ seam<n) :
    addr a i≠addr a seam := by
  intro H
  by_cases k : seam<n
  · have E := addr_inj a (by omega) k H
    omega
  · have E : seam=n := by omega
    have W : addr a seam=addr a 0 := by
      rw [E]
      apply Fin.ext
      simp [addr,Nat.add_mod_right]
    have eq := addr_inj a (by omega) (by omega) (H.trans W)
    omega

/-- One ordinary actual K5 release: provenance and vacancy are
read before the same mark, and simultaneous retained LD service
is included. The sole-header seam is a separate parallel case. -/
theorem ordinary_release {Tag : Type} (digits : Tag→BitVec 36) (atDigit : Nat→Tag)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (a e : Fin n) (seam width : Nat)
    (strip₀ : Strip B base a seam width) (strip : Strip B x a seam width)
    (root : a=(S.getD 0 fall).1)
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (m : Mode) (rel : ReleaseAt hp x e a seam (fun j=>S.getD j fall) len m)
    (good : Good anyTag len (project (fun k => S.getD k fall) x) (.out rel.k))
    (clean : OutClean len (project (fun k => S.getD k fall) x) (.out rel.k))
    (sep : e≠rightNeighbor e) (ordinary : 0<rel.i ∨ seam<n)
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (headFirst seam label))
    (old : RetainedMatches digits x (addr a seam) width s)
    (matched : UpstreamMatches digits x a seam label)
    (ldGate : ∀ j<width,(readLane (Sheet.index .ld) (x (addr (addr a seam) j)).long).gate=true)
    (ldPrep : NoLDPrep hp x (addr a seam) e width)
    (gate : (sample x a seam rel.i).gate=true)
    (frozen : (sample x a seam rel.i).frozen=.data (digits (atDigit rel.i)))
    (vacant : CutVacant x S fall len rel.k false)
    (pay : s.release.pending=atDigit rel.i::pending atDigit rel.i) :
    let q := deposit label rel.i (atDigit rel.i)
    ∃ t, t.release=(s.releaseOne (atDigit rel.i) (pending atDigit rel.i)).release ∧
      OrderedPrefix plan t (headFirst seam q) ∧ RetainedMatches digits (ring x e) (addr a seam) width t ∧
      UpstreamMatches digits (ring x e) a seam q := by
  dsimp only
  have cur : Unvisited S fall len rel.k false (addr a rel.i) :=
    ⟨rel.k,Nat.le_refl _,Nat.le_of_lt rel.strict,rel.ptr⟩
  obtain ⟨write,_,issued⟩ := deposit_at_cut hp digits (atDigit rel.i) chart a seam width rel.i rel.k strip₀
    rel.range cur e .right rel.markAt sep label matched vacant rel.win gate frozen _ P pay
  have ls := ordinary_ring hp digits (atDigit rel.i) chart same e a seam width rel.i rel.k rel.range strip₀ root
    (congrArg Prod.fst rel.ptr) good clean rel.markAt sep ordinary rel.win label matched write
  have notInto : rightNeighbor e≠addr a seam := by
    rw [rel.markAt]
    exact distinct_destination a rel.range strip.seam_le ordinary
  rcases noningress_classify hp digits x a e seam width strip sep notInto s plan _ size P old ldGate ldPrep
    with held|⟨k,d,E,held⟩
  · exact ⟨s.releaseOne (atDigit rel.i) (pending atDigit rel.i),rfl,issued,held,ls⟩
  · have rebase : ∀ (t : Ledger Tag) (u v : List Tag), OrderedStep s u t v → u=v →
        OrderedStep (s.releaseOne (atDigit rel.i) (pending atDigit rel.i)) (headFirst seam (deposit label rel.i (atDigit rel.i)))
          (t.releaseOne (atDigit rel.i) (pending atDigit rel.i)) (headFirst seam (deposit label rel.i (atDigit rel.i))) := by
      intro t u v J K
      cases J with
      | hold => exact .hold _ _
      | issue _ _ _ _ =>
        have N := congrArg List.length K
        simp only [List.length_append,List.length_cons,List.length_nil] at N
        omega
      | cross _ _ _ _ =>
        have N := congrArg List.length K
        simp only [List.length_cons] at N
        omega
      | interior _ j tag src dst =>
        rw [BStarCopyRightRetained.release_transfer_commute]
        exact .interior _ _ j tag src dst
    exact ⟨(s.transfer k d).releaseOne (atDigit rel.i) (pending atDigit rel.i),rfl,
      .mark issued (rebase _ _ _ E rfl),held,ls⟩

open BStarCopyRightMark (old_access new_access joined_spectator hop_no_effect rightNeighbor_inj)

private theorem last_mark {n : Nat} (a e : Fin n)
    (loc : rightNeighbor e=addr a 0) : e=addr a (n-1) := by
  have N : 0<n := Nat.zero_lt_of_lt a.isLt
  have wrap : addr a n=addr a 0 := by
    apply Fin.ext
    simp [addr,Nat.add_mod_right]
  apply rightNeighbor_inj
  rw [loc,←addr_next,show n-1+1=n by omega,wrap]

/-- Sole-header release with optional old cross on the same raw mark.
When the old hop is absent/blocked, only the fresh deposition occurs. -/
theorem sole_release {Tag : Type} (digits : Tag→BitVec 36) (tag : Tag)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (a e : Fin n) (width : Nat)
    (strip₀ : Strip B base a n width) (strip : Strip B x a n width)
    (root : a=(S.getD 0 fall).1)
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (m : Mode) (rel : ReleaseAt hp x e a n (fun j=>S.getD j fall) len m) (idx : rel.i=0)
    (good : Good anyTag len (project (fun k => S.getD k fall) x) (.out rel.k))
    (clean : OutClean len (project (fun k => S.getD k fall) x) (.out rel.k))
    (sep : e≠rightNeighbor e) (s : Ledger Tag) (plan : List Tag) (size : plan.length=width)
    (label : Nat→Option Tag) (P : OrderedPrefix plan s (headFirst n label))
    (old : RetainedMatches digits x (addr a n) width s)
    (matched : UpstreamMatches digits x a n label)
    (ldGate : (readLane (Sheet.index .ld) (x (addr (addr a n) 0)).long).gate=true)
    (lsGate : (sample x a n (n-1)).gate=true)
    (ldPrep : NoLDPrep hp x (addr a n) e width)
    (gate : (sample x a n 0).gate=true) (frozen : (sample x a n 0).frozen=.data (digits tag))
    (vacant : CutVacant x S fall len rel.k false)
    (pay : s.release.pending=tag::[]) :
    ∃ t q, t.release=(s.releaseOne tag []).release ∧ OrderedPrefix plan t (headFirst n q) ∧
      RetainedMatches digits (ring x e) (addr a n) width t ∧ UpstreamMatches digits (ring x e) a n q := by
  have loc : rightNeighbor e=addr a 0 := idx ▸ rel.markAt
  have ptr : S.getD rel.k fall=(addr a 0,5) := idx ▸ rel.ptr
  have last := last_mark a e loc
  have npos := strip.seam_pos
  have wp := strip.width_pos
  have N : 0<n := npos
  have high : n-1<n := by omega
  have neq : n-1≠0 := by
    intro Z
    apply sep
    exact (last.trans (congrArg (addr a) Z)).trans loc.symm
  have cur : Unvisited S fall len rel.k false (addr a 0) :=
    ⟨rel.k,Nat.le_refl _,Nat.le_of_lt rel.strict,ptr⟩
  obtain ⟨write,_,issued⟩ := deposit_at_cut hp digits tag chart a n width 0 rel.k strip₀
    npos cur e .right loc sep label matched vacant rel.win gate frozen [] P pay
  have behind : ∀ j≤0, Unvisited S fall len rel.k false (addr a j) := by
    intro j J
    have E : j=0 := by omega
    rw [E]
    exact cur
  have zero := empty_behind_cut digits x a n 0 len rel.k npos S fall label matched vacant behind 0 (by omega)
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let rsv := reserved (round g raw).prep
  let u := L Sheet.ls
  let v := R Sheet.ld
  let h := hop u v
  let dest := addr a n
  have C := dest_of_strip hp x a n width strip
  have wrap : dest=addr a 0 := by
    apply Fin.ext
    simp [dest,addr,Nat.add_mod_right]
  have into : rightNeighbor e=addr dest 0 :=
    loc.trans (wrap.symm.trans (Fin.ext (Nat.mod_eq_of_lt dest.isLt)).symm)
  have src : view raw u=sample x a n (n-1) := by
    rw [old_access]
    change readLane (Sheet.index .ls) (x e).long=_
    rw [last]
    simp only [sample,rail,if_pos high]
  have dst : view raw v=readLane (Sheet.index .ld) (x (addr dest 0)).long := by
    rw [old_access]
    change readLane (Sheet.index .ld) (x (rightNeighbor e)).long=_
    rw [into]
  have G : ((view raw u).gate && (view raw v).gate)=true := by rw [src,dst,lsGate,ldGate]; rfl
  have intoBoth : ((readLane (Sheet.index .ls) (x e).long).gate &&
      (readLane (Sheet.index .ld) (x (rightNeighbor e)).long).gate)=true := by
    rw [old_access x e u,old_access x e v] at G
    exact G
  have quiet (Q : h∉orderedData g rsv ∨ dataEffects g (view raw) h=[]) :
      ∃ t q, t.release=(s.releaseOne tag []).release ∧ OrderedPrefix plan t (headFirst n q) ∧
        RetainedMatches digits (ring x e) dest width t ∧ UpstreamMatches digits (ring x e) a n q := by
    have on (z : At Sheet) (Z : z=u ∨ z=v) (no : z∉rsv) :
        view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) z=view raw z := by
      refine joined_spectator hp (x e,x (rightNeighbor e)) z no ?_
      intro d D f F
      have M := data_lane_claim _ _ _ _ _ F
      have K : d=h := by
        have J := pair_claim strip (n-1) (by omega) rsv d (last ▸ D)
        have l : rail n (n-1)=.ls := if_pos high
        have r : rail n (n-1+1)=.ld := if_neg (by omega)
        rw [l,r] at J
        have K : u∈d.slots ∨ v∈d.slots := Z.elim (fun E=>.inl (E ▸ M)) (fun E=>.inr (E ▸ M))
        exact J K
      subst d
      rcases Q with A|A
      · exact A D
      · change (z,f)∈dataEffects g (view raw) h at F
        rw [A] at F
        exact List.not_mem_nil F
    have no := no_competing_prep hp chart same e a n width 0 rel.k npos strip₀ root
      (congrArg Prod.fst ptr) good clean (n-1) high neq .left last
    have A := on u (.inl rfl) no
    have V := on v (.inr rfl) (ldPrep 0 wp .right into)
    rw [new_access hp x e u sep,old_access x e u] at A
    rw [new_access hp x e v sep,old_access x e v] at V
    change readLane (Sheet.index .ld) (ring x e (rightNeighbor e)).long=
      readLane (Sheet.index .ld) (x (rightNeighbor e)).long at V
    rw [into] at V
    have retained := ingress_extend hp digits x dest e width C into sep s (s.releaseOne tag [])
      plan _ size P old ldPrep (V.symm ▸ old 0 wp) (fun _ _=>rfl)
    refine ⟨s.releaseOne tag [],deposit label 0 tag,rfl,issued,retained,?_⟩
    intro j J
    by_cases Z : j=0
    · subst j; rw [deposit,if_pos (rfl : 0=0)]; exact write
    · by_cases F : j=n-1
      · subst j
        unfold sample
        rw [rail,if_pos high,←last,deposit,if_neg Z]
        exact (congrArg Lane.mobile A).trans (by
          change (readLane (Sheet.index .ls) (x e).long).mobile=_
          have E := matched (n-1) high
          simpa only [sample,rail,if_pos high,←last] using E)
      · have E : addr a j≠e := by rw [last]; exact fun Q => F (addr_inj a J high Q)
        have D : addr a j≠rightNeighbor e := by rw [loc]; exact fun Q => Z (addr_inj a J npos Q)
        have frame : ring x e (addr a j)=x (addr a j) := by simp [AllSizeS1Geometry.step,E,D]
        simpa only [sample,frame,deposit,if_neg Z] using matched j J
  by_cases chosen : h∈orderedData g rsv
  · cases head : label (n-1) with
    | none =>
      have no : (view raw u).mobile=.empty := by rw [src,matched _ high,head]; rfl
      exact quiet (.inr (hop_no_effect g _ _ _ (.inl no)))
    | some headTag =>
      cases empty : (s.cells 0).mobile with
      | some z =>
        have no : (view raw v).mobile≠.empty := by rw [dst,(old 0 wp).1,empty]; intro Q; contradiction
        exact quiet (.inr (hop_no_effect g _ _ _ (.inr ⟨G,no⟩)))
      | none =>
        have ret : retains g v=true := by
          have inR : g.2.inside=true := by
            change (longGeometry B (x (rightNeighbor e))).inside=true
            rw [into]
            exact C.inside 0 wp
          simp [v,retains,R,inR]
        obtain ⟨U,D,P'⟩ := sole_header_cross_ring hp digits headTag tag e a width strip loc sep label
          matched head zero write [] P pay chosen ret intoBoth (into.symm ▸ old 0 wp) empty
        have H := ingress_extend hp digits x dest e width C into sep s ((s.receiveFirst headTag).releaseOne tag [])
          plan _ size P old ldPrep (into ▸ D) (by intro j J; simp [Ledger.receiveFirst, Ledger.releaseOne,J])
        exact ⟨(s.receiveFirst headTag).releaseOne tag [],deposit (clearLast label n) 0 tag,rfl,P',H,U⟩
  · exact quiet (.inl chosen)

end L4.BStarCopyLeftMixed
