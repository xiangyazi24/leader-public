import Leader.L4.BStarCopyLeftInjectionMark

namespace L4.BStarCopyLeftCollector
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongPrep BStarLongCommandData
open BStarCopyFIFO BStarCopyFenceSaturation BStarCopyMarkedLedger
open BStarCopyLeftStrip BStarCopyLeftMark BStarCopyLeftDeposit BStarCopyLeftInjectionMark
open BStarCopyRightStrip (addr addr_next addr_inj)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A single raw mark may require two ledger events, in old-head
then fresh-tail order, never a second physical step. -/
inductive Delta {T : Type} : Ledger T → List T → Ledger T → List T → Prop
  | one {s t u v} : OrderedStep s u t v → Delta s u t v
  | parallel {s t f u v w} : OrderedStep s u t v → OrderedStep t v f w → Delta s u f w

theorem lift_delta {T : Type} {plan : List T} {s t : Ledger T} {u v : List T}
    (P : OrderedPrefix plan s u) (M : Delta s u t v) : OrderedPrefix plan t v := by
  cases M with
  | one D => exact .mark P D
  | parallel D E => exact .mark (.mark P D) E

/-- Actual raw-mark witnesses retain the packed old/new relation,
with ghost updates justified by a bounded ledger delta. The caller
does not pick another physical edge to realize the delta. -/
structure MarkStep {T : Type} (digits : T→BitVec 36) (x : X) (e a : Fin n) (seam : Nat)
    (s t : Ledger T) (old new : Nat→Option T) : Prop where
  physical : UpstreamMatches digits (step x e) a seam new
  bookkeeping : Delta s (headFirst seam old) t (headFirst seam new)

theorem mark_hold {T : Type} (digits : T→BitVec 36) (x : X) (e a : Fin n) (seam : Nat)
    (s : Ledger T) (q : Nat→Option T) (M : UpstreamMatches digits x a seam q)
    (frame : ∀ j<seam, (sample (step x e) a seam j).mobile=(sample x a seam j).mobile) :
    MarkStep hp digits x e a seam s s q q :=
  ⟨fun j J => (frame j J).trans (M j J), .one (.hold _ _)⟩

/-- An idle left projection may contain unrestricted unrelated
physical work. Only emitted effects on the tracked LS slots matter. -/
theorem mark_hold_actual {T : Type} (digits : T→BitVec 36) (x : X) (e a : Fin n)
    (seam : Nat) (s : Ledger T) (q : Nat→Option T)
    (M : UpstreamMatches digits x a seam q) (sep : e≠rightNeighbor e)
    (quiet : let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      ∀ j<seam, ∀ z : At Sheet, site e z.side=addr a j → z.occurrence=.ls →
        z∉reserved (round g raw).prep ∧
        ∀ d∈orderedData g (reserved (round g raw).prep),
          ∀ leaf,(z,leaf)∉dataEffects g (view raw) d) :
    MarkStep hp digits x e a seam s s q q := by
  apply mark_hold hp digits x e a seam s q M
  intro j J
  apply congrArg Lane.mobile
  apply spectator hp x e a seam j sep
  dsimp only
  intro z Z E
  rw [rail,if_pos J] at E
  exact quiet j J z Z E

theorem mark_hop {T : Type} (digits : T→BitVec 36) (tag : T) (x : X)
    (a : Fin n) (seam width i : Nat) (s : Ledger T) (q : Nat→Option T)
    (C : Strip B x a seam width) (I : i+1<seam)
    (M : UpstreamMatches digits x a seam q)
    (fromTag : q i=some tag) (empty : q (i+1)=none) :
    let e := addr a i
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    e≠rightNeighbor e →
    hop (L .ls) (R .ls)∈orderedData g (reserved (round g raw).prep) →
    ((view raw (L .ls)).gate && (view raw (R .ls)).gate)=true →
    MarkStep hp digits x e a seam s s q (moveTag q i tag) := by
  dsimp only
  intro sep chosen gate
  have H := ring_upstream hp digits tag x a seam width i I C q M fromTag empty sep chosen gate
  refine ⟨H,?_⟩
  have eq := congrArg List.reverse (upstreamWord_move seam i I q tag fromTag empty)
  change headFirst seam (moveTag q i tag)=headFirst seam q at eq
  rw [eq]
  exact .one (.hold _ _)

theorem mark_deposit {T : Type} (digits : T→BitVec 36) (tag : T)
    (x : X) (e a : Fin n) (seam i : Nat) (I : i<seam)
    (s : Ledger T) (q : Nat→Option T) (todo : List T) (pending : s.release.pending=tag::todo)
    (vacant : ∀ j≤i,q j=none)
    (physical : UpstreamMatches digits (step x e) a seam (deposit q i tag)) :
    MarkStep hp digits x e a seam s (s.releaseOne tag todo) q (deposit q i tag) := by
  refine ⟨physical,?_⟩
  rw [append_at_cut q seam i I tag vacant]
  exact .one (.issue _ _ _ _ pending)

theorem mark_cross {T : Type} (digits : T→BitVec 36) (tag : T)
    (x : X) (e a : Fin n) (seam : Nat) (pos : 0<seam)
    (s : Ledger T) (q : Nat→Option T) (head : q (seam-1)=some tag)
    (vacant : (s.cells 0).mobile=none)
    {plan : List T} (P : OrderedPrefix plan s (headFirst seam q))
    (physical : UpstreamMatches digits (step x e) a seam (clearLast q seam)) :
    MarkStep hp digits x e a seam s (s.receiveFirst tag) q (clearLast q seam) := by
  refine ⟨physical,?_⟩
  have E := pop_last q seam pos tag head
  have c := BStarCopyUpstreamTags.old_head_credit tag _ (E ▸ P)
  rw [E]
  exact .one (.cross _ _ _ vacant c)

theorem mark_parallel {T : Type} (digits : T→BitVec 36) (head fresh : T)
    (x : X) (e a : Fin n) (seam : Nat) (pos : 0<seam)
    (s : Ledger T) (q : Nat→Option T) (todo : List T)
    (H : q (seam-1)=some head) (V : q 0=none)
    (vacant : (s.cells 0).mobile=none) (pending : s.release.pending=fresh::todo)
    {plan : List T} (P : OrderedPrefix plan s (headFirst seam q))
    (physical : UpstreamMatches digits (step x e) a seam (deposit (clearLast q seam) 0 fresh)) :
    MarkStep hp digits x e a seam s ((s.receiveFirst head).releaseOne fresh todo)
      q (deposit (clearLast q seam) 0 fresh) := by
  refine ⟨physical,?_⟩
  have E := pop_last q seam pos head H
  have c := BStarCopyUpstreamTags.old_head_credit head _ (E ▸ P)
  have empty : ∀ j≤0,clearLast q seam j=none := by
    intro j J
    have E : j=0 := by omega
    simp [E,clearLast,V]
  rw [E,append_at_cut _ seam 0 pos fresh empty]
  exact .parallel (.cross _ _ _ vacant c) (.issue _ _ _ _ pending)

/-- A crossing without simultaneous source deposition. When the
destination header is also the source header (seam=n), only its
right LS prep reservation must be absent. With distinct headers,
no reservation premise on that untracked lane is needed. -/
theorem mark_cross_actual {T : Type} (digits : T→BitVec 36) (tag : T)
    (x : X) (a : Fin n) (seam width : Nat) (s : Ledger T) (q : Nat→Option T)
    (C : Strip B x a seam width) (M : UpstreamMatches digits x a seam q)
    (head : q (seam-1)=some tag) (vacant : (s.cells 0).mobile=none)
    {plan : List T} (P : OrderedPrefix plan s (headFirst seam q)) :
    let e := addr a (seam-1)
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let dst := fun y : X => readLane (Sheet.index .ld) (y (rightNeighbor e)).long
    e≠rightNeighbor e →
    (seam=n → R .ls∉reserved (round g raw).prep) →
    hop (L .ls) (R .ld)∈orderedData g (reserved (round g raw).prep) →
    ((readLane (Sheet.index .ls) (x e).long).gate && (dst x).gate)=true →
    Compatible digits (s.cells 0) (dst x) →
    MarkStep hp digits x e a seam s (s.receiveFirst tag) q (clearLast q seam) ∧
      Compatible digits ((s.receiveFirst tag).cells 0) (dst (step x e)) := by
  dsimp only
  intro sep prep chosen gates agree
  let e := addr a (seam-1)
  have pos := C.seam_pos
  have nb := C.seam_le
  have ne : L Sheet.ls≠R .ld := by intro H; cases congrArg At.side H
  have N : rightNeighbor e=addr a seam := by
    rw [←addr_next a (seam-1),show seam-1+1=seam by omega]
  have h : (oldPair B x e).2.axes.h6=true := by
    change oldH6 B x (rightNeighbor e)=true
    rw [N]; exact C.dest_header
  have ret : retains (oldPair B x e) (R .ld)=true := by
    have inside : (oldPair B x e).2.inside=true := by
      change (longGeometry B (x (rightNeighbor e))).inside=true
      rw [N]; exact C.ld_in _ (by omega) (by have := C.width_pos; omega)
    simp [retains,R,inside]
  have fromTag := M (seam-1) (by omega)
  unfold sample at fromTag
  rw [rail,if_pos (show seam-1<seam by omega),head] at fromTag
  have E := pop_last q seam pos tag head
  obtain ⟨_,send,receive⟩ := BStarCopyUpstreamTags.ring_cross_head hp digits tag _ (E ▸ P)
    x e sep (hop (L .ls) (R .ld)) (R .ld) rfl rfl chosen ne ret gates fromTag agree vacant
  refine ⟨mark_cross hp digits tag x e a seam pos s q head vacant P ?_,receive⟩
  intro j J
  by_cases eq : j=seam-1
  · subst j
    rw [clearLast,if_pos (rfl : seam-1=seam-1)]
    unfold sample
    rw [rail,if_pos (show seam-1<seam by omega)]
    exact send
  · have full := spectator hp x e a seam j sep (by
      dsimp only
      intro z loc sh
      rw [rail,if_pos J] at sh
      have zEq : z=(⟨z.side,.ls⟩ : At Sheet) := by cases z; simp_all
      cases S : z.side with
      | left =>
        rw [S] at loc
        change addr a (seam-1)=addr a j at loc
        exact (eq ((addr_inj a (by omega) (by omega) loc).symm)).elim
      | right =>
        rw [S] at loc
        change rightNeighbor e=addr a j at loc
        have limit : seam=n := by
          by_cases A : seam<n
          · have K := addr_inj a A (by omega) (N.symm.trans loc)
            omega
          · omega
        have A : z=R .ls := zEq.trans (by rw [S]; rfl)
        rw [A]
        refine ⟨prep limit,?_⟩
        intro d chosen leaf effect
        have slot := data_lane_claim _ _ _ _ _ effect
        have raw := BStarLongFenceTopology.selected_data_raw _ _ _ chosen
        have noSrc := (no_right_send _ _ raw).1
        have noDst : d.destination≠some (R .ls) := by
          intro D
          have K := (raw_ls_receive _ _ D).mp raw
          exact Bool.noConfusion (h.symm.trans K.1)
        cases dst : d.destination with
        | none =>
          have F : R Sheet.ls=d.source := by simpa [Claim.slots,dst] using slot
          exact noSrc F.symm
        | some u =>
          have F : R Sheet.ls=d.source ∨ R Sheet.ls=u := by simpa [Claim.slots,dst] using slot
          rcases F with F|F
          · exact noSrc F.symm
          · exact noDst (dst.trans (congrArg some F.symm)))
    rw [full,clearLast,if_neg eq]
    exact M j J

/-- Fold the per-mark exact projection across the original raw word.
The missing scheduler-side obligation is producing this witness on
every reachable mark, not the ordered ghost induction. -/
theorem fold {T : Type} (digits : T→BitVec 36) (plan : List T)
    (a : Fin n) (seam : Nat) (ready : X→Ledger T→(Nat→Option T)→Prop)
    (project : ∀ x e s q, ready x s q → UpstreamMatches digits x a seam q →
      OrderedPrefix plan s (headFirst seam q) →
      ∃ t v, MarkStep hp digits x e a seam s t q v ∧ ready (step x e) t v)
    (x : X) (w : List (Fin n)) (s : Ledger T) (q : Nat→Option T)
    (R : ready x s q) (M : UpstreamMatches digits x a seam q)
    (P : OrderedPrefix plan s (headFirst seam q)) :
    ∃ t v, ready (run x w) t v ∧ UpstreamMatches digits (run x w) a seam v ∧
      OrderedPrefix plan t (headFirst seam v) := by
  induction w generalizing x s q with
  | nil => exact ⟨s,q,R,M,P⟩
  | cons e w ih =>
    obtain ⟨t,v,J,R'⟩ := project x e s q R M P
    exact ih (step x e) t v R' J.physical (lift_delta P J.bookkeeping)

end L4.BStarCopyLeftCollector
