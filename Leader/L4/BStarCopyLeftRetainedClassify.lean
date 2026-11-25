import Leader.L4.BStarCopyLeftRetained

namespace L4.BStarCopyLeftRetainedClassify
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyRightStrip (addr addr_next addr_inj)
open BStarCopyRightMark (old_access new_access joined_spectator hop_no_effect rightNeighbor_inj)
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyFIFO BStarCopyFenceSaturation
open BStarCopyMarkedLedger BStarCopyLeftRetained
open BStarCopyRightRetained (Dest)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

def NoLDPrep (x : X) (root e : Fin n) (width : Nat) : Prop :=
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let rs := reserved (round (oldPair B x e) raw).prep
  ∀ q<width, ∀ s, site e s=addr root q → (⟨s,.ld⟩ : At Sheet)∉rs

private theorem body_claim {x : X} {base : Fin n} {seam width i : Nat}
    (C : Strip B x base seam width) (h : seam≤i) (I : i+1<seam+width)
    (rs : List (At Sheet)) (d : DataClaim) (D : d∈orderedData (oldPair B x (addr base i)) rs)
    (s : Side) (M : (⟨s,.ld⟩ : At Sheet)∈d.slots) : d=hop (L .ld) (R .ld) := by
  have P : L (rail seam i)∈d.slots ∨ R (rail seam (i+1))∈d.slots := by
    rw [rail,if_neg (by omega : ¬ i<seam),rail,if_neg (by omega : ¬ i+1<seam)]
    cases s
    · exact .inl M
    · exact .inr M
  simpa only [rail,if_neg (by omega : ¬ i<seam),if_neg (by omega : ¬ i+1<seam)] using
    pair_claim C i I rs d D P

/-- Strong whole retained projection away from the one ingress mark.
A tagged old mobile moves iff the actual selected RD row has old
vacancy; otherwise every retained lane frames. Deliberately leaves
the upstream projection wholly independent, even on alias marks. -/
theorem noningress_classify {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (base e : Fin n) (seam width : Nat) (S : Strip B x base seam width)
    (sep : e≠rightNeighbor e) (excludeIngress : rightNeighbor e≠addr base seam)
    (s : Ledger Tag) (plan up : List Tag) (size : plan.length=width)
    (P : OrderedPrefix plan s up)
    (old : RetainedMatches digits x (addr base seam) width s)
    (gate : ∀ j<width, (readLane (Sheet.index .ld) (x (addr (addr base seam) j)).long).gate=true)
    (prep : NoLDPrep hp x (addr base seam) e width) :
    RetainedMatches digits (ring x e) (addr base seam) width s ∨
      ∃ (k : Nat) (tag : Tag),
        OrderedStep s up (s.transfer k tag) up ∧
        RetainedMatches digits (ring x e) (addr base seam) width (s.transfer k tag) := by
  let root := addr base seam
  have C := dest_of_strip hp x base seam width S
  have fit := C.fit
  have pos := C.pos
  by_cases inside : ∃ j, j+1<width ∧ e=addr root j
  · obtain ⟨j,jw,rfl⟩ := inside
    let mark := addr root j
    let g := oldPair B x mark
    let raw : Pair (BitVec LW) := ((x mark).long,(x (rightNeighbor mark)).long)
    let u := L Sheet.ld
    let v := R Sheet.ld
    let d := hop u v
    let rs := reserved (round g raw).prep
    let k := j
    have Rj : rightNeighbor mark=addr root (j+1) := (addr_next root j).symm
    have toEdge : addr base (seam+j)=mark := by
      have E : addr root 0=root := Fin.ext (Nat.mod_eq_of_lt root.isLt)
      exact (addr_from base seam j).trans (by simpa only [Nat.zero_add,E] using (addr_from root 0 j).symm)
    have hsrc : (view raw u).mobile=encode digits (s.cells k).mobile := by
      rw [old_access x mark u]
      exact (old j (by omega)).1
    have hdst : (view raw v).mobile=encode digits (s.cells (k+1)).mobile := by
      rw [old_access x mark v]
      change (readLane (Sheet.index .ld) (x (rightNeighbor mark)).long).mobile=_
      rw [Rj]
      exact (old (j+1) jw).1
    have gu : (view raw u).gate=true := by
      rw [old_access x mark u]; exact gate _ (by omega)
    have gv : (view raw v).gate=true := by
      rw [old_access x mark v]
      change (readLane (Sheet.index .ld) (x (rightNeighbor mark)).long).gate=true
      rw [Rj]; exact gate _ jw
    have G : ((view raw u).gate && (view raw v).gate)=true := by simp [gu,gv]
    have blocked (Hq : d∉orderedData g rs ∨ dataEffects g (view raw) d=[]) :
        RetainedMatches digits (ring x mark) root width s := by
      intro q qw
      have frameSide (side : Side) (loc : site mark side=addr root q) :
          readLane (Sheet.index .ld) (ring x mark (addr root q)).long =
            readLane (Sheet.index .ld) (x (addr root q)).long := by
        let slot : At Sheet := ⟨side,.ld⟩
        have Hs := joined_spectator hp (x mark,x (rightNeighbor mark)) slot (prep q qw side loc)
        have Hs := Hs (fun c M l A => by
          have T := data_lane_claim g (view raw) c slot l A
          have Eq := body_claim hp S (i:=seam+j) (by omega) (by omega) rs c
            (toEdge.symm ▸ M) side (by exact T)
          change c=d at Eq
          subst c
          rcases Hq with Hq|Hq
          · exact Hq M
          · change (slot,l)∈dataEffects g (view raw) d at A
            rw [Hq] at A
            exact List.not_mem_nil A)
        change view (Pair.map LargeSite.long (largePair B (x mark,x (rightNeighbor mark)))) slot = view raw slot at Hs
        rw [new_access hp x mark slot sep,old_access x mark slot] at Hs
        change readLane (Sheet.index .ld) (ring x mark (site mark side)).long =
          readLane (Sheet.index .ld) (x (site mark side)).long at Hs
        rwa [loc] at Hs
      change Compatible digits (s.cells q) (readLane (Sheet.index .ld) (ring x mark (addr root q)).long)
      by_cases Lp : addr root q=mark
      · rw [frameSide .left Lp.symm]; exact old q qw
      · by_cases Rp : addr root q=rightNeighbor mark
        · rw [frameSide .right Rp.symm]; exact old q qw
        · rw [show ring x mark (addr root q)=x (addr root q) from by simp [AllSizeS1Geometry.step,Lp,Rp]]
          exact old q qw
    by_cases M : d∈orderedData g rs
    · cases a : (s.cells k).mobile with
      | none =>
        apply Or.inl (blocked (.inr ?_))
        apply hop_no_effect
        exact .inl (hsrc.trans (by rw [a]; rfl))
      | some tag =>
        cases b : (s.cells (k+1)).mobile with
        | none =>
          have R := retained_internal hp digits x (addr base seam) width j jw C s plan up P old tag a b sep M G
          exact .inr ⟨k,tag,.interior s up k tag a b,R.2⟩
        | some other =>
          apply Or.inl (blocked (.inr ?_))
          apply hop_no_effect
          exact .inr ⟨G,by rw [hdst,b]; intro H; contradiction⟩
    · exact .inl (blocked (.inl M))
  · apply Or.inl
    intro j jw
    have noR : addr root j≠rightNeighbor e := by
      intro E
      by_cases zero : j=0
      · subst j
        have A : addr root 0=root := Fin.ext (Nat.mod_eq_of_lt root.isLt)
        rw [A] at E
        exact excludeIngress E.symm
      · have T : e=addr root (j-1) := by
          apply rightNeighbor_inj
          rw [←addr_next,show j-1+1=j by omega]
          exact E.symm
        exact inside ⟨j-1,by omega,T⟩
    by_cases noL : addr root j=e
    · by_cases eq : j=width-1
      · subst j
        rw [retained_last_frame hp digits x root e width C s plan up size P old noL.symm sep
          (prep _ (by omega) .left noL.symm)]
        exact old _ jw
      · exact (inside ⟨j,by omega,noL.symm⟩).elim
    · rw [show ring x e (addr root j)=x (addr root j) from by simp [AllSizeS1Geometry.step,noL,noR]]
      exact old j jw

/-- At the actual ingress edge only retained cell zero may acquire
an arrival. If width=n, the other endpoint is exactly the terminal
LAST, whose old mobile is empty by the ordered ledger. The terminal
frame is proved on this very mark, not by excluding site aliasing. -/
theorem ingress_extend {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (root e : Fin n) (width : Nat) (C : Dest B x root width)
    (into : rightNeighbor e=addr root 0) (sep : e≠rightNeighbor e)
    (s t : Ledger Tag) (plan up : List Tag) (size : plan.length=width)
    (P : OrderedPrefix plan s up) (old : RetainedMatches digits x root width s)
    (prep : NoLDPrep hp x root e width)
    (atZero : Compatible digits (t.cells 0)
      (readLane (Sheet.index .ld) (ring x e (addr root 0)).long))
    (rest : ∀ j, j≠0 → t.cells j=s.cells j) :
    RetainedMatches digits (ring x e) root width t := by
  have pos := C.pos
  have fit := C.fit
  intro j J
  by_cases Z : j=0
  · subst j; exact atZero
  have R : addr root j≠rightNeighbor e := by
    rw [into]
    exact fun H => Z (addr_inj root (by omega) (by omega) H)
  by_cases Lh : addr root j=e
  · have A : addr root (j+1)=addr root 0 := by rw [addr_next,Lh,into]
    have N : j+1=n := by
      by_cases less : j+1<n
      · have K := addr_inj root less (by omega) A
        omega
      · omega
    have Jw : j=width-1 := by omega
    subst j
    have Frame := retained_last_frame hp digits x root e width C s plan up size P old Lh.symm sep
      (prep _ (by omega) .left Lh.symm)
    change Compatible digits (t.cells (width-1))
      (readLane (Sheet.index .ld) (ring x e (addr root (width-1))).long)
    rw [Frame,rest _ Z]
    exact old _ J
  · have Frame : ring x e (addr root j)=x (addr root j) := by
      simp [AllSizeS1Geometry.step,Lh,R]
    change Compatible digits (t.cells j) (readLane (Sheet.index .ld) (ring x e (addr root j)).long)
    rw [Frame,rest _ Z]
    exact old j J

end L4.BStarCopyLeftRetainedClassify
