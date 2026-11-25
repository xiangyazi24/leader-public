import Leader.L4.BStarFenceChartData
import Leader.L4.BStarCommitOperands
import Leader.L4.BStarClearanceDataChart

namespace L4.BStarFenceReceiverChart
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireAnchors
open BStarAcquireLiteralChain BStarResetChartTouch BStarAcquireRailCoverage
open BStarClearanceDataChart BStarLongFiberOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def digitFrom (i : Fin n) : Nat → Fin n
  | 0 => i
  | d+1 => rightNeighbor (digitFrom i d)

/-- The actual receiver strip started at an old H6 header contains every
ordinal below the width: no intervening H6 seam may truncate it. -/
theorem digit_from {base : X} {hh : ∃ i,oldH6 B base i=true} {i : Fin n}
    (H : oldH6 B base i=true) (width : Nat)
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1) :
    ∀ d, d<width →
      oldOrdinal B base hh (digitFrom i d)=d ∧
      word (oldH6 B base) (digitFrom i d)=word (oldH6 B base) i := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨(ordinal_zero _ hh _).mpr H,rfl⟩
  | succ d ih =>
    intro hd
    obtain ⟨O,W⟩ := ih (by omega)
    have next : oldH6 B base (rightNeighbor (digitFrom i d))=false := by
      cases E : oldH6 B base (rightNeighbor (digitFrom i d))
      · rfl
      · have J := notShort _ E
        omega
    have A := ordinal_body (oldH6 B base) hh (digitFrom i d) next
    change oldOrdinal B base hh (rightNeighbor (digitFrom i d))=
      oldOrdinal B base hh (digitFrom i d)+1 at A
    refine ⟨A.trans (congrArg (·+1) O),?_⟩
    have Q := right_word (oldH6 B base) (digitFrom i d)
    rw [next] at Q
    simp only [Bool.toNat_false,Int.natCast_zero,Int.add_zero] at Q
    obtain ⟨a,b⟩ := word_range (oldH6 B base) (digitFrom i d) hh
    rw [Int.emod_eq_of_lt a b] at Q
    exact Q.trans W

/-- K7 at the last inside digit and K10 at the corresponding header
belong to the same command owner and to its two actual data sheets.
These are the last receivers in the increasing LD and decreasing RD
ordinal traversals, respectively. -/
theorem endpoints {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1) :
    let i := (S.getD len fall).1
    let last := digitFrom i (width-1)
    (S.getD len fall).2=10 ∧ oldOrdinal B base hh i=0 ∧
    (longGeometry B (base i)).inside=true ∧
    dataOwner (oldH6 B base) i .rd=o.val ∧
    oldOrdinal B base hh last+1=width ∧ (longGeometry B (base last)).inside=true ∧
    dataOwner (oldH6 B base) last .ld=o.val ∧
    ∃ k<len, S.getD k fall=(last,7) := by
  dsimp only
  let i := (S.getD len fall).1
  let last := digitFrom i (width-1)
  have e : S.getD len fall=(i,10) := Prod.ext rfl (C.terminal ▸ rfl)
  obtain ⟨H,P,_⟩ := endpoint_spec (oldH6 B base) hh o 10
  rw [←C.terminal] at H P
  change oldH6 B base i=true at H
  change commandOwner (oldH6 B base) i 10=o.val at P
  have O : oldOrdinal B base hh i=0 := (ordinal_zero _ hh _).mpr H
  have I : (longGeometry B (base i)).inside=true := by rw [inside,O,decide_eq_true_eq]; exact hw
  obtain ⟨L,W⟩ := digit_from hp H width notShort (width-1) (by omega)
  change oldOrdinal B base hh last=width-1 at L
  change word (oldH6 B base) last=word (oldH6 B base) i at W
  have IL : (longGeometry B (base last)).inside=true := by rw [inside,L,decide_eq_true_eq]; omega
  have OL : commandOwner (oldH6 B base) last 7=o.val := by
    unfold commandOwner at P ⊢
    rw [W]
    exact P
  have M := C.cover (last,7) (by rfl) OL
  obtain ⟨k,hk,K⟩ := List.getElem_of_mem M
  have KL : S.getD k fall=(last,7) := (List.getElem_eq_getD _).symm.trans K
  have lenS := C.length
  have KLT : k<len := by
    by_cases Z : k=len
    · subst k
      exact False.elim ((by decide : (10 : Fin 11)≠7) (congrArg Prod.snd (e.symm.trans KL)))
    · omega
  exact ⟨congrArg Prod.snd e,O,I,P,by change oldOrdinal B base hh last+1=width; omega,IL,OL,k,KLT,KL⟩

open BStarAcquireForwardTrace BStarGeneratedOwner BStarNativeAttemptReceipts
open BStarNativeReceiptTape BStarFenceChartData BStarLongPackets BStarLongPrep BStarResetMarkAdapter
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private def LaneReady (d : Lane) : Prop := d.mobile=.empty ∧ ∃ z,d.retained=.data z

private theorem view_site (x : Fin n → BitVec LW) (e : Fin n) (s : Side) (d : Sheet) :
    view (x e,x (rightNeighbor e)) ⟨s,d⟩=readLane (Sheet.index d) (x (site e s)) := by
  cases s <;> rfl

/-- An accepted physical FENCE on the settled command chart finds
both actual last COPY receivers, in the old states of that same tour. -/
theorem accepted_receivers {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (ack : Fin n)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j => S.getD j fall) len (run x w) ack 11) :
    let i := (S.getD len fall).1
    let l := digitFrom i (width-1)
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n),
      w=pre++mark::(gap++turn::back) ∧
      let left := run x pre
      let right := run (step left mark) gap
      let ld := readLane (Sheet.index .ld) (left l).long
      let rd := readLane (Sheet.index .rd) (right i).long
      (ld.mobile=.empty ∧ ∃ z,ld.retained=.data z) ∧
      (rd.mobile=.empty ∧ ∃ z,rd.retained=.data z) := by
  dsimp only
  obtain ⟨_,_,I,_,_,L,_,k,kl,addr⟩ := endpoints hp C hw inside notShort
  have lin : (longGeometry B (base (S.getD k fall).1)).inside=true := by rw [addr]; exact L
  obtain ⟨pre,gap,back,mark,turn,cl,cr,_,_,E,_,_,lAt,rAt,_,_,_,_,ld,rd⟩ :=
    data_of_accepted_fence hp C sep k kl (congrArg Prod.snd addr) lin I w ack T H
  have lsite := (congrArg Prod.fst addr).symm.trans (congrArg Prod.fst lAt)
  have rsite := congrArg Prod.fst rAt
  refine ⟨pre,gap,back,mark,turn,E,?_,?_⟩
  · change digitFrom (S.getD len fall).1 (width-1)=site mark cl.source.side at lsite
    rw [lsite]
    have V := view_site (fun i => (run x pre i).long) mark cl.source.side .ld
    change LaneReady _ at ld ⊢
    exact V ▸ ld
  · change (S.getD len fall).1=site turn cr.source.side at rsite
    rw [rsite]
    have V := view_site (fun i => (run (step (run x pre) mark) gap i).long) turn cr.source.side .rd
    change LaneReady _ at rd ⊢
    exact V ▸ rd

end L4.BStarFenceReceiverChart
