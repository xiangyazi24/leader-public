import Leader.L4.BStarCopyLeftRetainedClassify

namespace L4.BStarCopyLeftDataSweep
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftDeposit BStarCopyLeftInjectionMark
open BStarCopyLeftRetained BStarCopyLeftRetainedClassify BStarCopyFIFO BStarCopyFenceSaturation
open BStarCopyRightStrip (addr addr_next addr_inj)
open BStarCopyRightMark (old_access new_access joined_spectator hop_no_effect rightNeighbor_inj)
open BStarCopyMarkedLedger

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

def NoLSPrep (x : X) (base e : Fin n) (seam : Nat) : Prop :=
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  ∀ j<seam, ∀ s, site e s=addr base j →
    (⟨s,.ls⟩ : At Sheet)∉reserved (round (oldPair B x e) raw).prep

open BStarCopyLeftCollector

/-- All nonseam data marks either preserve the ordered LS stream or
move one mobile to its adjacent vacant LS position. -/
theorem upstream_nonseam {T : Type} (digits : T→BitVec 36)
    (x : X) (base e : Fin n) (seam width : Nat) (C : Strip B x base seam width)
    (sep : e≠rightNeighbor e) (notSeam : e≠addr base (seam-1))
    (q : Nat→Option T) (old : UpstreamMatches digits x base seam q)
    (gate : ∀ j<seam, (sample x base seam j).gate=true)
    (prep : NoLSPrep hp x base e seam) :
    ∃ v, headFirst seam v=headFirst seam q ∧ UpstreamMatches digits (ring x e) base seam v := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let h := hop (L .ls) (R .ls)
  let rs := reserved (round g raw).prep
  have nb := C.seam_le
  have touch (j : Nat) (J : j<seam) (a : At Sheet) (loc : site e a.side=addr base j)
      (ls : a.occurrence=.ls) (d : DataClaim) (M : d∈orderedData g rs) (S : a∈d.slots) :
      (∃ i, i+1<seam ∧ e=addr base i) ∧ d=h := by
    have A : a=⟨a.side,.ls⟩ := by cases a; simp_all
    cases sd : a.side with
    | left =>
      rw [sd] at loc
      change e=addr base j at loc
      have hi : j+1<seam := by
        by_cases last : j=seam-1
        · exact (notSeam (last ▸ loc)).elim
        · omega
      have aL : a=L .ls := A.trans (by rw [sd]; rfl)
      have Q : L (rail seam j)∈d.slots := by rw [rail,if_pos J,←aL]; exact S
      have E := pair_claim (x:=x) C j (by have := C.width_pos; omega) rs d (loc ▸ M) (.inl Q)
      refine ⟨⟨j,hi,loc⟩,?_⟩
      simpa only [rail,if_pos J,if_pos hi] using E
    | right =>
      rw [sd] at loc
      change rightNeighbor e=addr base j at loc
      have aR : a=R .ls := A.trans (by rw [sd]; rfl)
      have rawM := BStarLongFenceTopology.selected_data_raw _ _ _ M
      have dst : d.destination=some (R .ls) := by
        rw [aR] at S
        cases D : d.destination with
        | none =>
          have Y : R Sheet.ls=d.source := by simpa [Claim.slots,D] using S
          exact ((no_right_send _ _ rawM).1 Y.symm).elim
        | some b =>
          have Y : R Sheet.ls=d.source ∨ R Sheet.ls=b := by simpa [Claim.slots,D] using S
          rcases Y with Y|Y
          · exact ((no_right_send _ _ rawM).1 Y.symm).elim
          · exact (congrArg some Y.symm)
      obtain ⟨body,E⟩ := (raw_ls_receive _ _ dst).mp rawM
      have jp : 0<j := by
        cases j with
        | succ j => omega
        | zero =>
          have F : addr base 0=base := Fin.ext (Nat.mod_eq_of_lt base.isLt)
          change oldH6 B x (rightNeighbor e)=false at body
          rw [loc,F,C.source_header] at body
          contradiction
      have ee : e=addr base (j-1) := by
        apply rightNeighbor_inj
        rw [←addr_next,show j-1+1=j by omega]
        exact loc
      exact ⟨⟨j-1,by omega,ee⟩,E⟩
  have quiet (inactive : ¬ (∃ i, i+1<seam ∧ e=addr base i) ∨
      h∉orderedData g rs ∨ dataEffects g (view raw) h=[]) :
      UpstreamMatches digits (ring x e) base seam q := by
    intro j J
    have frame := spectator hp x e base seam j sep (by
      dsimp only
      intro a A Ls
      rw [rail,if_pos J] at Ls
      have ne := prep j J a.side A
      have eq : a=⟨a.side,.ls⟩ := by cases a; simp_all
      refine ⟨eq.symm ▸ ne,?_⟩
      intro d D f F
      obtain ⟨I,H⟩ := touch j J a A Ls d D (data_lane_claim _ _ _ _ _ F)
      subst d
      rcases inactive with no|no|no
      · exact no I
      · exact no D
      · rw [no] at F; exact List.not_mem_nil F)
    rw [frame]
    exact old j J
  by_cases I : ∃ i, i+1<seam ∧ e=addr base i
  · obtain ⟨i,hi,eq⟩ := I
    by_cases sel : h∈orderedData g rs
    · have Lc : site e .left=addr base i := eq
      have Rc : site e .right=addr base (i+1) := eq ▸ (addr_next base i).symm
      have rewriteView (side : Side) (j : Nat) (J : j<seam) (E : site e side=addr base j) :
          view raw ⟨side,.ls⟩=sample x base seam j := by
        rw [old_access]
        change readLane (Sheet.index .ls) (x (site e side)).long=_
        rw [E]
        simp only [sample,rail,if_pos J]
      have Q := rewriteView .left i (by omega) Lc
      have V := rewriteView .right (i+1) hi Rc
      have G : ((view raw (L .ls)).gate && (view raw (R .ls)).gate)=true := by
        change ((view raw ⟨.left,.ls⟩).gate && (view raw ⟨.right,.ls⟩).gate)=true
        rw [Q,V,gate i (by omega),gate _ hi]; rfl
      cases D : q i with
      | none =>
        refine ⟨q,rfl,quiet (.inr (.inr (hop_no_effect g _ _ _ (.inl ?_))))⟩
        exact Q ▸ ((old i (by omega)).trans (by rw [D]; rfl))
      | some tag =>
        cases E : q (i+1) with
        | none =>
          have F := ring_upstream hp digits tag x base seam width i hi C q old D E
            (eq ▸ sep) (eq ▸ sel) (eq ▸ G)
          exact ⟨moveTag q i tag,congrArg List.reverse (upstreamWord_move _ _ hi _ _ D E),eq.symm ▸ F⟩
        | some other =>
          refine ⟨q,rfl,quiet (.inr (.inr (hop_no_effect g _ _ _ (.inr ⟨G,?_⟩))))⟩
          change (view raw ⟨.right,.ls⟩).mobile≠.empty
          rw [V,old _ hi,E]
          intro F; contradiction
    · exact ⟨q,rfl,quiet (.inr (.inl sel))⟩
  · exact ⟨q,rfl,quiet (.inl I)⟩

/-- Full combined old-pair data classifier; any projection may
coexist with work in the other projection of the very same mark. -/
theorem data_mark {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (base e : Fin n) (seam width : Nat) (S : Strip B x base seam width)
    (sep : e≠rightNeighbor e)
    (s : Ledger Tag) (plan : List Tag) (size : plan.length=width) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (headFirst seam label))
    (old : RetainedMatches digits x (addr base seam) width s)
    (matched : UpstreamMatches digits x base seam label)
    (ldGate : ∀ j<width,(readLane (Sheet.index .ld) (x (addr (addr base seam) j)).long).gate=true)
    (lsGate : ∀ j<seam,(sample x base seam j).gate=true)
    (ldPrep : NoLDPrep hp x (addr base seam) e width)
    (lsPrep : NoLSPrep hp x base e seam) :
    ∃ t q, t.release=s.release ∧ OrderedPrefix plan t (headFirst seam q) ∧
      RetainedMatches digits (ring x e) (addr base seam) width t ∧
      UpstreamMatches digits (ring x e) base seam q := by
  have pos := S.seam_pos
  have wp := S.width_pos
  have nb := S.seam_le
  have seamAt : rightNeighbor (addr base (seam-1))=addr base seam := by
    rw [←addr_next,show seam-1+1=seam by omega]
  by_cases atSeam : e=addr base (seam-1)
  · subst e
    let e := addr base (seam-1)
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let rs := reserved (round g raw).prep
    let u := L Sheet.ls
    let v := R Sheet.ld
    let h := hop u v
    let root := addr base seam
    have C := dest_of_strip hp x base seam width S
    have ez : addr root 0=root := Fin.ext (Nat.mod_eq_of_lt root.isLt)
    have into : rightNeighbor e=addr root 0 := seamAt.trans ez.symm
    have oldH : g.2.axes.h6=true := by
      change oldH6 B x (rightNeighbor e)=true
      rw [seamAt]; exact S.dest_header
    have ut : view raw u=sample x base seam (seam-1) := by
      rw [old_access]
      change readLane (Sheet.index .ls) (x e).long=_
      simp only [sample,rail,if_pos (show seam-1<seam by omega)]
      rfl
    have vt : view raw v=readLane (Sheet.index .ld) (x (addr root 0)).long := by
      rw [old_access]
      change readLane (Sheet.index .ld) (x (rightNeighbor e)).long=_
      rw [into]
    have G : ((view raw u).gate && (view raw v).gate)=true := by
      rw [ut,vt,lsGate _ (by omega),ldGate _ wp]; rfl
    have touch (d : DataClaim) (D : d∈orderedData g rs) (T : u∈d.slots ∨ v∈d.slots) : d=h := by
      have ll : rail seam (seam-1)=.ls := if_pos (by omega)
      have rr : rail seam (seam-1+1)=.ld := if_neg (by omega)
      have pair := pair_claim S (seam-1) (by omega) rs d D
      rw [ll,rr] at pair
      exact pair T
    have rightQuiet (d : DataClaim) (D : d∈orderedData g rs) :
        (R Sheet.ls)∉d.slots := by
      intro M
      have rawM := BStarLongFenceTopology.selected_data_raw _ _ _ D
      have noS := (no_right_send _ _ rawM).1
      have noD : d.destination≠some (R .ls) := fun F =>
        Bool.noConfusion (oldH.symm.trans (((raw_ls_receive _ _ F).mp rawM).1))
      rcases List.mem_cons.mp M with E|E
      · exact noS E.symm
      · cases dst : d.destination with
        | none => simp [dst] at E
        | some w =>
          have F : R Sheet.ls=w := by simpa only [dst,Option.toList_some,List.mem_singleton] using E
          exact noD (dst.trans (congrArg some F.symm))
    have hold (quiet : h∉orderedData g rs ∨ dataEffects g (view raw) h=[]) :
        RetainedMatches digits (ring x e) root width s ∧
        UpstreamMatches digits (ring x e) base seam label := by
      have frame (a : At Sheet) (A : a=u ∨ a=v) (prep : a∉rs) :
          view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a=view raw a := by
        refine joined_spectator hp (x e,x (rightNeighbor e)) a prep ?_
        intro d D l F
        have sl := data_lane_claim _ _ _ _ _ F
        have b := touch d D (A.elim (fun E => .inl (E ▸ sl)) (fun E => .inr (E ▸ sl)))
        subst d
        rcases quiet with N|N
        · exact N D
        · change (a,l)∈dataEffects g (view raw) h at F
          rw [N] at F; exact List.not_mem_nil F
      have J := frame v (.inr rfl) (ldPrep 0 wp .right into)
      rw [new_access hp x e v sep,old_access x e v] at J
      change readLane (Sheet.index .ld) (ring x e (rightNeighbor e)).long =
        readLane (Sheet.index .ld) (x (rightNeighbor e)).long at J
      rw [into] at J
      refine ⟨ingress_extend hp digits x root e width C into sep s s plan _ size P old ldPrep
        (J.symm ▸ old 0 wp) (fun _ _ => rfl),?_⟩
      intro j jfit
      have F := spectator hp x e base seam j sep (by
        dsimp only
        intro a A Ls
        rw [rail,if_pos jfit] at Ls
        have eq : a=⟨a.side,.ls⟩ := by cases a; simp_all
        refine ⟨eq.symm ▸ lsPrep j jfit a.side A,?_⟩
        intro d D l E
        have sl := data_lane_claim _ _ _ _ _ E
        cases sd : a.side with
        | right =>
          have right : a=R .ls := eq.trans (by rw [sd]; rfl)
          exact rightQuiet d D (right ▸ sl)
        | left =>
          have left : a=u := eq.trans (by rw [sd]; rfl)
          have eqD := touch d D (.inl (left ▸ sl))
          subst d
          rcases quiet with N|N
          · exact N D
          · rw [N] at E; exact List.not_mem_nil E)
      rw [F]; exact matched j jfit
    by_cases chosen : h∈orderedData g rs
    · cases hsrc : label (seam-1) with
      | none =>
        have empty : (view raw u).mobile=.empty := by
          rw [ut,matched _ (by omega),hsrc]; rfl
        have H := hold (.inr (hop_no_effect g _ _ _ (.inl empty)))
        exact ⟨s,label,rfl,P,H⟩
      | some tag =>
        cases vacant : (s.cells 0).mobile with
        | none =>
          have prepHeader : seam=n → R .ls∉rs := by
            intro E
            have wrap : addr base seam=addr base 0 := by
              rw [E]; apply Fin.ext; simp [addr,Nat.add_mod_right]
            exact lsPrep 0 pos .right (seamAt.trans wrap)
          obtain ⟨L,D⟩ := mark_cross_actual hp digits tag x base seam width s label S matched hsrc vacant P
            sep prepHeader chosen
            (by
              rw [old_access x e u,old_access x e v] at G
              exact G)
            (into.symm ▸ old 0 wp)
          have T := ingress_extend hp digits x root e width C into sep s (s.receiveFirst tag) plan _
            size P old ldPrep (into ▸ D) (by intro j J; simp [Ledger.receiveFirst,J])
          exact ⟨s.receiveFirst tag,clearLast label seam,rfl,lift_delta P L.bookkeeping,T,L.physical⟩
        | some b =>
          have nonempty : (view raw v).mobile≠.empty := by
            rw [vt,(old 0 wp).1,vacant]; intro E; contradiction
          have H := hold (.inr (hop_no_effect g _ _ _ (.inr ⟨G,nonempty⟩)))
          exact ⟨s,label,rfl,P,H⟩
    · exact ⟨s,label,rfl,P,hold (.inl chosen)⟩
  · have notInto : rightNeighbor e≠addr base seam := fun E =>
      atSeam (rightNeighbor_inj (E.trans seamAt.symm))
    obtain ⟨q,E,H⟩ := upstream_nonseam hp digits x base e seam width S sep atSeam label matched lsGate lsPrep
    rcases noningress_classify hp digits x base e seam width S sep notInto s plan _ size P old ldGate ldPrep with F|⟨j,tag,D,F⟩
    · exact ⟨s,q,rfl,E.symm ▸ P,F,H⟩
    · exact ⟨s.transfer j tag,q,rfl,E.symm ▸ OrderedPrefix.mark P D,F,H⟩

structure DataReady (x : X) (base e : Fin n) (seam width : Nat) : Prop where
  strip : Strip B x base seam width
  ldGate : ∀ j<width,(readLane (Sheet.index .ld) (x (addr (addr base seam) j)).long).gate=true
  lsGate : ∀ j<seam,(sample x base seam j).gate=true
  ldPrep : NoLDPrep hp x (addr base seam) e width
  lsPrep : NoLSPrep hp x base e seam

local notation "play" => BStarResetSchedule.run ring

/-- Sweep the original unreduced data-only raw word. Geometry, gates
and absence of this owner's prep are the readiness interface. No
scheduler checklist or nonaliasing between LS and LD sites is used. -/
theorem data_word {Tag : Type} (digits : Tag→BitVec 36)
    (x : X) (w : List (Fin n)) (base : Fin n) (seam width : Nat)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (plan : List Tag) (size : plan.length=width)
    (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (headFirst seam label))
    (old : RetainedMatches digits x (addr base seam) width s)
    (matched : UpstreamMatches digits x base seam label)
    (ready : ∀ a e b,w=a++e::b → DataReady hp (play x a) base e seam width) :
    ∃ t post, t.release=s.release ∧ OrderedPrefix plan t (headFirst seam post) ∧
      RetainedMatches digits (play x w) (addr base seam) width t ∧
      UpstreamMatches digits (play x w) base seam post := by
  induction w generalizing x s label with
  | nil => exact ⟨s,label,rfl,P,old,matched⟩
  | cons e w ih =>
    obtain ⟨S,A,LS,C,D⟩ := ready [] e w rfl
    obtain ⟨t,q,R,ind,held,mobile⟩ := data_mark hp digits x base e seam width S (sep e)
      s plan size label P old matched A LS C D
    obtain ⟨v,m,M,F,H,Q⟩ := ih (ring x e) t q ind held mobile
      (fun a f b E => ready (e::a) f b (congrArg (List.cons e) E))
    exact ⟨v,m,M.trans R,F,H,Q⟩

#print axioms data_word
#print axioms data_mark
#print axioms upstream_nonseam
end L4.BStarCopyLeftDataSweep
