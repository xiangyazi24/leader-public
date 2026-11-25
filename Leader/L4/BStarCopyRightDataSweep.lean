import Leader.L4.BStarCopyRightRetainedClassify

namespace L4.BStarCopyRightDataSweep
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip BStarCopyRightMark BStarCopyFIFO BStarCopyFenceSaturation
open BStarCopyMarkedLedger BStarCopyRightRetained BStarCopyRightRetainedClassify

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

/-- Prep exclusion on the upstream projection only. At PC11 this
follows from authenticated owner opcode and exact lack of prepOf 11. -/
def NoUpPrep (x : X) (base e : Fin n) (seam tail : Nat) : Prop :=
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  ∀ j, 0<j → j≤tail → ∀ s, site e s=addr base j →
    (⟨s,rail seam j⟩ : At Sheet)∉reserved (round (oldPair B x e) raw).prep

/-- Non-ingress data mark: the independent upstream projection
classifies exactly ordered stutter or an adjacent hop onto vacancy,
for all physical marks even if also incident to retained RD slots. -/
theorem upstream_noningress {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (base e : Fin n) (seam tail : Nat) (C : Strip B x base seam tail)
    (sep : e≠rightNeighbor e) (excludeIngress : e≠addr base 0)
    (label : Nat→Option Tag) (old : MobileMatches digits x base seam tail label)
    (gate : ∀ j, 0<j → j≤tail → (readLane (Sheet.index (rail seam j)) (x (addr base j)).long).gate=true)
    (prep : NoUpPrep hp x base e seam tail) :
    ∃ after, stripWord tail after=stripWord tail label ∧
      MobileMatches digits (ring x e) base seam tail after := by
  by_cases inside : ∃ i, 0<i ∧ i<tail ∧ e=addr base i
  · obtain ⟨i,ip,it,rfl⟩ := inside
    let mark := addr base i
    let g := oldPair B x mark
    let raw : Pair (BitVec LW) := ((x mark).long,(x (rightNeighbor mark)).long)
    let rs := reserved (round g raw).prep
    let u := R (rail seam (i+1))
    let v := L (rail seam i)
    let h := hop u v
    have V : site mark v.side=addr base i := rfl
    have U : site mark u.side=addr base (i+1) := (addr_next base i).symm
    have land (a : At Sheet) (A : a=u ∨ a=v) :
        a∉rs := by
      rcases A with rfl|rfl
      · exact prep _ (by omega) (by omega) .right U
      · exact prep _ ip (by omega) .left V
    have source : (view raw u).mobile=encode digits (label (i+1)) := by
      rw [old_access x mark u,U]
      exact old _ (by omega) (by omega)
    have target : (view raw v).mobile=encode digits (label i) := by
      rw [old_access x mark v,V]
      exact old _ ip (by omega)
    have gu : (view raw u).gate=true := by
      rw [old_access x mark u,U]
      exact gate _ (by omega) (by omega)
    have gv : (view raw v).gate=true := by
      rw [old_access x mark v,V]
      exact gate _ ip (by omega)
    have both : ((view raw u).gate && (view raw v).gate)=true := by simp [gu,gv]
    have quiet (inactive : h∉orderedData g rs ∨ (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) :
      MobileMatches digits (ring x mark) base seam tail label := by
      intro j jp jt
      have Q := strip_pair_frame hp x base seam tail i it C inactive
      by_cases first : j=i
      · subst j
        have f := Q v (.inr rfl) (land v (.inr rfl))
        change view (Pair.map LargeSite.long (largePair B (x mark,x (rightNeighbor mark)))) v=view raw v at f
        rw [new_access hp x mark v sep,old_access x mark v,V] at f
        exact (congrArg Lane.mobile f).trans (old _ jp jt)
      · by_cases second : j=i+1
        · subst j
          have f := Q u (.inl rfl) (land u (.inl rfl))
          change view (Pair.map LargeSite.long (largePair B (x mark,x (rightNeighbor mark)))) u=view raw u at f
          rw [new_access hp x mark u sep,old_access x mark u,U] at f
          exact (congrArg Lane.mobile f).trans (old _ jp jt)
        · rw [ring_other_positions hp x base i j tail it jp jt C.tail_lt first second]
          exact old _ jp jt
    by_cases selected : h∈orderedData g rs
    · cases s : label (i+1) with
      | none =>
        exact ⟨label,rfl,quiet (.inr (.inl (source.trans (by rw [s]; rfl))))⟩
      | some tag =>
        cases d : label i with
        | none =>
          exact ⟨swapTag label i tag,stripWord_swap tail i ip it label tag s d,
            ring_transport hp digits tag x base seam tail i ip it C h label old s d sep selected rfl both⟩
        | some q =>
          exact ⟨label,rfl,quiet (.inr (.inr ⟨both,by rw [target,d]; intro Z; contradiction⟩))⟩
    · exact ⟨label,rfl,quiet (.inl selected)⟩
  · refine ⟨label,rfl,?_⟩
    intro j jp jt
    by_cases eq : e=addr base j
    · have endEq : j=tail := by
        by_cases why : j=tail
        · exact why
        · exfalso
          exact inside ⟨j,jp,by omega,eq⟩
      subst j
      subst e
      let raw : Pair (BitVec LW) := ((x (addr base tail)).long,(x (rightNeighbor (addr base tail))).long)
      let slot := L (rail seam tail)
      have F := joined_tail_frame hp x base seam tail C (prep tail jp jt .left rfl)
      change view (Pair.map LargeSite.long (largePair B (x (addr base tail),x (rightNeighbor (addr base tail))))) slot =
        view raw slot at F
      rw [new_access hp x (addr base tail) slot sep,old_access x (addr base tail) slot] at F
      exact (congrArg Lane.mobile F).trans (old _ jp jt)
    · have pred : e≠addr base (j-1) := by
        intro E
        by_cases first : j=1
        · subst j
          exact excludeIngress E
        · exact inside ⟨j-1,by omega,by omega,E⟩
      rw [ring_exterior_frame hp x base e j jp eq pred]
      exact old j jp jt

theorem ingress_quiet {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root base : Fin n) (width seam tail : Nat)
    (C : Dest B x root width) (U : Strip B x base seam tail)
    (join : addr base 0=addr root (width-1))
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width)
    (label : Nat→Option Tag) (P : OrderedPrefix plan s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (matched : MobileMatches digits x base seam tail label) :
    let e := addr base 0
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    let u := R (rail seam 1)
    let v := L (rail seam 0)
    e≠rightNeighbor e →
    NoRDPrep hp x root e width →
    (hop u v∉orderedData g (reserved (round g raw).prep) ∨
      (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) →
    RetainedMatches digits (ring x e) root width s ∧
      (NoUpPrep hp x base e seam tail → MobileMatches digits (ring x e) base seam tail label) := by
  dsimp only
  intro sep prep inactive
  let e := addr base 0
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let u := R (rail seam 1)
  let v := L (rail seam 0)
  have vrd : rail seam 0=.rd := if_pos U.seam_pos
  have widthP := C.pos
  have T : 0<tail := Nat.lt_of_lt_of_le U.seam_pos U.seam_le_tail
  have Q := strip_pair_frame hp x base seam tail 0 T U inactive
  have upLoc : site e u.side=addr base 1 := (addr_next base 0).symm
  have vLoc : site e v.side=addr root (width-1) := join
  have notPrepV := prep (width-1) (by omega) .left join
  change (⟨Side.left,Sheet.rd⟩ : At Sheet)∉reserved (round (oldPair B x e) raw).prep at notPrepV
  have Nv : v∉reserved (round (oldPair B x e) raw).prep := by
    change L (rail seam 0)∉reserved (round (oldPair B x e) raw).prep
    rw [vrd]
    exact notPrepV
  have F := Q v (.inr rfl) Nv
  change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) v=view raw v at F
  rw [new_access hp x e v sep,old_access x e v,vLoc] at F
  have frameHead : readLane (Sheet.index .rd) (ring x e (addr root (width-1))).long =
      readLane (Sheet.index .rd) (x (addr root (width-1))).long := by
    change readLane (Sheet.index (rail seam 0)) (ring x e (addr root (width-1))).long =
      readLane (Sheet.index (rail seam 0)) (x (addr root (width-1))).long at F
    rwa [vrd] at F
  refine ⟨?_,?_⟩
  · intro j jw
    by_cases same : j=width-1
    · subst j
      rw [frameHead]
      exact old _ jw
    · have fit := C.fit
      have noL : addr root j≠e := fun H => same (addr_inj root (by omega) (by omega) (H.trans join))
      by_cases right : addr root j=rightNeighbor e
      · by_cases zero : j=0
        · subst j
          rw [retained_header_frame hp digits x root e width C s plan _ size P old right.symm sep
            (prep 0 jw .right right.symm)]
          exact old 0 jw
        · have prev : e=addr root (j-1) := by
            apply rightNeighbor_inj
            rw [←addr_next root (j-1),show j-1+1=j by omega]
            exact right.symm
          have impossible := addr_inj root (by omega) (by omega) (join.symm.trans prev)
          omega
      · rw [show ring x e (addr root j)=x (addr root j) from by simp [AllSizeS1Geometry.step,noL,right]]
        exact old _ jw
  · intro prepUp j jp jt
    by_cases same : j=1
    · subst j
      have N := prepUp 1 jp jt .right upLoc
      have Z := Q u (.inl rfl) N
      change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) u=view raw u at Z
      rw [new_access hp x e u sep,old_access x e u,upLoc] at Z
      exact (congrArg Lane.mobile Z).trans (matched 1 jp jt)
    · rw [ring_other_positions hp x base 0 j tail T jp jt U.tail_lt (by omega) same]
      exact matched _ jp jt

/-- Complete all-label data-only classifier. Each physical mark may
cause an independent upstream swap and a retained transfer; neither
projection pretends the other rail is idle. Intended for the PC11
portion after actual absence of new INJECT has been proved. -/
theorem data_mark {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root base e : Fin n) (width seam tail : Nat)
    (C : Dest B x root width) (U : Strip B x base seam tail)
    (join : addr base 0=addr root (width-1)) (sep : e≠rightNeighbor e)
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width)
    (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (matched : MobileMatches digits x base seam tail label)
    (rdGate : ∀ j<width, (readLane (Sheet.index .rd) (x (addr root j)).long).gate=true)
    (upGate : ∀ j, 0<j → j≤tail → (readLane (Sheet.index (rail seam j)) (x (addr base j)).long).gate=true)
    (rdPrep : NoRDPrep hp x root e width) (upPrep : NoUpPrep hp x base e seam tail) :
    ∃ t labels, t.release=s.release ∧ OrderedPrefix plan t (stripWord tail labels) ∧
      RetainedMatches digits (ring x e) root width t ∧
      MobileMatches digits (ring x e) base seam tail labels := by
  by_cases atHead : e=addr base 0
  · subst e
    let e := addr base 0
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let u := R (rail seam 1)
    let v := L (rail seam 0)
    let h := hop u v
    have vrd : rail seam 0=.rd := if_pos U.seam_pos
    have lp := C.pos
    have pos : 0<tail := Nat.lt_of_lt_of_le U.seam_pos U.seam_le_tail
    have uLoc : site e u.side=addr base 1 := (addr_next base 0).symm
    have vLoc : site e v.side=addr root (width-1) := join
    have source : (view raw u).mobile=encode digits (label 1) := by
      rw [old_access x e u,uLoc]
      exact matched 1 (by omega) (by omega)
    have target : (view raw v).mobile=encode digits (s.cells 0).mobile := by
      rw [old_access x e v,vLoc]
      change (readLane (Sheet.index (rail seam 0)) (x (addr root (width-1))).long).mobile=_
      rw [vrd]
      have T := (old (width-1) (by omega)).1
      rwa [Nat.sub_self] at T
    have gu : (view raw u).gate=true := by
      rw [old_access x e u,uLoc]
      exact upGate 1 (by omega) (by omega)
    have gv : (view raw v).gate=true := by
      rw [old_access x e v,vLoc]
      change (readLane (Sheet.index (rail seam 0)) (x (addr root (width-1))).long).gate=true
      rw [vrd]
      exact rdGate (width-1) (by omega)
    have G : ((view raw u).gate && (view raw v).gate)=true := by simp [gu,gv]
    have stays (n : h∉orderedData g (reserved (round g raw).prep) ∨
      (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) :
        ∃ t labels, t.release=s.release ∧ OrderedPrefix plan t (stripWord tail labels) ∧
          RetainedMatches digits (ring x e) root width t ∧ MobileMatches digits (ring x e) base seam tail labels := by
      obtain ⟨R,U⟩ := ingress_quiet hp digits x root base width seam tail C U join s plan size label P old matched
        sep rdPrep n
      exact ⟨s,label,rfl,P,R,U upPrep⟩
    by_cases selected : h∈orderedData g (reserved (round g raw).prep)
    · cases fromTag : label 1 with
      | none => exact stays (.inr (.inl (source.trans (by rw [fromTag]; rfl))))
      | some tag =>
        cases vacant : (s.cells 0).mobile with
        | none =>
          have M := ingress_cross hp digits x root base width seam tail C U join s plan size label P old matched
            tag fromTag vacant sep rdPrep (by simpa only [h,u,v,vrd] using selected)
            (by simpa only [v,vrd] using G)
          exact ⟨s.receiveFirst tag,clearHead label,rfl,M⟩
        | some t => exact stays (.inr (.inr ⟨G,by rw [target,vacant]; intro K; contradiction⟩))
    · exact stays (.inl selected)
  · obtain ⟨lab,E,F⟩ := upstream_noningress hp digits x base e seam tail U sep atHead label matched upGate upPrep
    rcases noningress_classify hp digits x root e width C sep (join ▸ atHead) s plan _ size P old rdGate rdPrep with R|⟨i,tag,step,R⟩
    · exact ⟨s,lab,rfl,E.symm ▸ P,R,F⟩
    · have new : OrderedPrefix plan (s.transfer i tag) (stripWord tail label) := .mark P step
      exact ⟨s.transfer i tag,lab,rfl,E.symm ▸ new,R,F⟩

structure DataReady (x : X) (root base e : Fin n) (width seam tail : Nat) : Prop where
  dest : Dest B x root width
  strip : Strip B x base seam tail
  rdGate : ∀ j<width, (readLane (Sheet.index .rd) (x (addr root j)).long).gate=true
  upGate : ∀ j, 0<j → j≤tail → (readLane (Sheet.index (rail seam j)) (x (addr base j)).long).gate=true
  rdPrep : NoRDPrep hp x root e width
  upPrep : NoUpPrep hp x base e seam tail

local notation "play" => BStarResetSchedule.run ring

/-- Ordered exact right ledger over the whole unreduced PC11 data
word, including waits, nonown physical marks, and simultaneous
independent lane moves. No selected-move checklist is supplied. -/
theorem data_word {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (w : List (Fin n)) (root base : Fin n) (width seam tail : Nat)
    (join : addr base 0=addr root (width-1))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (plan : List Tag) (size : plan.length=width)
    (s : Ledger Tag) (labels : Nat→Option Tag)
    (P : OrderedPrefix plan s (stripWord tail labels))
    (old : RetainedMatches digits x root width s)
    (matched : MobileMatches digits x base seam tail labels)
    (ready : ∀ a e b,w=a++e::b → DataReady hp (play x a) root base e width seam tail) :
    ∃ t post, t.release=s.release ∧ OrderedPrefix plan t (stripWord tail post) ∧
      RetainedMatches digits (play x w) root width t ∧ MobileMatches digits (play x w) base seam tail post := by
  induction w generalizing x s labels with
  | nil => exact ⟨s,labels,rfl,P,old,matched⟩
  | cons e w ih =>
    obtain ⟨C,U,rg,ug,rp,up⟩ := ready [] e w rfl
    obtain ⟨t,q,R,ind,held,mobile⟩ := data_mark hp digits x root base e width seam tail C U join (sep e)
      s plan size labels P old matched rg ug rp up
    obtain ⟨v,m,M,A,H,Q⟩ := ih (ring x e) t q ind held mobile
      (fun a f b E => ready (e::a) f b (congrArg (List.cons e) E))
    exact ⟨v,m,M.trans R,A,H,Q⟩

end L4.BStarCopyRightDataSweep
