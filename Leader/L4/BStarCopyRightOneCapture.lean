import Leader.L4.BStarCopyRightLoadCoverage

namespace L4.BStarCopyRightOneCapture
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongEvents BStarLongDoor BStarLongCommandData
open BStarCopyRightStrip BStarCopyRightAuthority BStarCopyRightK2Past BStarCopyRightLoadCoverage
open BStarCopyLoadHistory BStarCopyLoadCarry BStarCopyOperand BStarCopyOwnedFrozen
open BStarAcquireVisitOrder BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireLiteralChain
open BStarResetChartTouch BStarClearanceDataChart BStarAcquireAnchors BStarResetMarkAdapter
open BStarSeparatingRail BStarAcquireForwardTrace BStarAcquireHistoryReturn BStarResetChartService
open BStarLongPackets BStarLongCommand

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem busy_append {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {a b c : Cursor} {u v : List (Fin n)}
    (P : BusyOnly hp base addr len op x a u b)
    (Q : BusyOnly hp base addr len op (play x u) b v c) :
    BusyOnly hp base addr len op x a (u++v) c := by
  induction P with
  | nil _ => exact Q
  | cons I E _ ih => exact .cons I E (ih Q)

/-- A single concrete ISSUE8 capture picks one bank for every RS slot
of the original complete LOAD tour. For each source the resulting
frozen packet is the immutable old bank at that source's real K2
mark. No per-source launch witnesses or caller-supplied visit lists. -/
theorem common_original_bank {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam tail : Nat) (strip : Strip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 8 (.back 0))) :
    ∃ (lead : List (Fin n)) (launch : Fin n) (suffix : List (Fin n)) (bank : Fin 3),
      w=lead++launch::suffix ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      bank.val=(captures.read ((play x lead) (S.getD 0 fall).1).long).toNat % 4 ∧
      let y := ring (play x lead) launch
      ∀ i, seam≤i → i≤tail →
        ∃ (pre : List (Fin n)) (rest : List (Fin n)) (k : Nat),
          suffix=pre++(addr a i)::rest ∧ k<len ∧ S.getD k fall=(addr a i,2) ∧
          Event hp (fun j=>S.getD j fall) len (play y pre) (addr a i)
            (.busy 8 (.out k)) (.busy 8 (.out (k+1))) ∧
          (readLane (Sheet.index .rs) (ring (play y pre) (addr a i) (addr a i)).long).frozen=
            oldBankPacket ((play y pre) (addr a i)).long bank := by
  obtain ⟨lead,suffix,launch,W,D,Launch,pc8,T⟩ := from_idle hp G
  let y := ring (play x lead) launch
  let root := (S.getD 0 fall).1
  let old : BitVec LW := ((play x lead) root).long
  let u := (captures.read old).toNat
  have launchCopy := Launch
  obtain ⟨_,arg,init,snap⟩ := launchCopy
  change initial (ctrlOp.read old).toNat old=some arg at init
  change (ctrlOp.read old).toNat=8 at pc8
  rw [pc8] at init
  obtain ⟨argEq,validArg⟩ := issue_load_operand _ _ init
  have valid : selTriple u=true := by rw [argEq] at validArg; exact validArg
  have width : u<64 := (captures.read old).isLt
  obtain ⟨bank,_,idxBank⟩ := captured_operand_index u width valid true
  have root0 := (root_header hp chart (busy_start hp T).1.1).2
  have start : project (fun j=>S.getD j fall) y 0=.forward (payload u) := by
    change atSite (y root).long (S.getD 0 fall).2=_
    rw [root0]
    have F := congrArg (fun z : (Token × BitVec 2) × BitVec 9 => z.1.1) snap
    change atSite (y root).long 0=forward (ctrlOp.read old).toNat arg at F
    rw [pc8] at F
    exact F.trans (load_issue_payload old arg init)
  refine ⟨lead,launch,suffix,bank,W,D,idxBank,?_⟩
  dsimp only
  intro i lo hi
  obtain ⟨k,kl,idx⟩ := rs_ord hp chart a seam tail strip ownerHead i lo hi
  obtain ⟨pre,e,rest,R,part,ev,after⟩ := busy_crosses hp T kl 0 rfl (Nat.zero_le _)
  let z := play y pre
  have cur := busy_end hp part
  have part' := busy_append hp part (.cons cur ev (.nil (busy_start hp after)))
  have trail' := busy_load_word hp chart sep part' u width valid 0 (k+1) rfl rfl start
  have afterF := load_word_carries hp trail' u width valid start
  rw [BStarResetSchedule.run_append] at afterF
  have q : project (fun j=>S.getD j fall) (ring z e) (k+1)=.forward (payload u) := afterF
  obtain ⟨cl,_,f,selected,_,src,_⟩ := BStarNumericChronology.ring_departure
    hp chart e (sep e) 8 k kl cur.1 cur.2.1 cur.2.2 (payload u) q rfl
  have kc : cl.source.occurrence=2 := congrArg Prod.snd (src.symm.trans idx)
  have mem : cl∈orderedCommands (oldPair B z e) := by
    rw [←actualOffers_claims _ ((z e).long,(z (rightNeighbor e)).long)]
    exact List.mem_map.mpr ⟨_,selected,rfl⟩
  have raw := raw_k2 (oldPair B z e) cl mem kc
  have srcL : cl.source=L 2 := by rw [raw]; cases (oldPair B z e).2.axes.h6 <;> rfl
  have nd : cl.kind≠.door := by rw [raw]; cases (oldPair B z e).2.axes.h6 <;> decide
  have loc := congrArg Prod.fst (src.symm.trans idx)
  have ee : e=addr a i := by rwa [srcL] at loc
  have inside : (longGeometry B (z e)).inside=true := by
    have same := congrArg (fun z : Bool × Bool × Bool => z.2.1) (cur.1.1 e)
    exact same.symm.trans (ee.symm ▸ strip.rs_in i lo hi)
  have own := (strip_same_owner strip i hi).trans ownerHead
  have rs : rail seam i=.rs := if_neg (by omega)
  rw [rs,←ee] at own
  have tr := busy_load_word hp chart sep part u width valid 0 k rfl rfl start
  have Z : (root,0)=S.getD 0 fall := Prod.ext rfl root0.symm
  have loadWord : LoadWord hp y (root,0) pre (address e cl.source) := by
    rw [Z,←src]; exact tr
  obtain ⟨actualBank,bk,F⟩ := pointed_freeze_from_launch hp chart Launch pc8 pre e .left true cl
    (sep e) k loadWord cur src.symm own mem nd srcL inside
  have one : actualBank=bank := Fin.ext (bk.trans idxBank.symm)
  subst actualBank
  exact ⟨pre,rest,k,ee ▸ R,kl,idx,ee ▸ ev,ee ▸ F⟩

end L4.BStarCopyRightOneCapture
