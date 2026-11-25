import Leader.L4.BStarCopyRightLoadCoverage
import Leader.L4.BStarCopyLeftInjectionMark

namespace L4.BStarCopyLeftOneCapture
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongEvents BStarLongDoor BStarLongCommandData
open BStarCopyRightStrip (addr)
open BStarCopyLeftStrip BStarCopyLeftInjectionMark BStarCopyRightLoadCoverage
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

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- R.K0 is the non-advancing source door; selected K0 departures
with a destination are exactly the left local K0. -/
theorem k0_link_left (g : Pair LongGeometry) (C : CommandClaim) (d : At (Fin 11))
    (chosen : C∈orderedCommands g) (occ : C.source.occurrence=0)
    (dest : C.destination=some d) : C.source=L 0 ∧ C.kind≠.door := by
  let yes (C : CommandClaim) : Bool :=
    (C.source.occurrence != 0 || C.destination.isNone) ||
      (C.source == L 0 && C.kind != .door)
  have A (I J H K : Bool) :
      (commandClaims (geo false I J,geo H K false)).all yes=true := by
    cases I <;> cases J <;> cases H <;> cases K <;> decide +kernel
  have raw := BStarLongFenceTopology.selected_command_raw _ _ chosen
  have P := List.all_eq_true.mp (A g.1.inside g.1.last g.2.axes.h6 g.2.inside) C raw
  simpa [yes,occ,dest] using P

theorem ls_ord {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (a : Fin n) (seam width i : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1) (hi : i<seam) :
    ∃ k<len, S.getD k fall=(addr a i,0) := by
  have O := (endpoint_spec (oldH6 B base) hh o 0).2.1
  rw [←chart.root,←root] at O
  have own : commandOwner (oldH6 B base) (addr a i) 0=o.val := by
    unfold commandOwner at O ⊢
    rw [ls_same_word hp strip hh i hi]
    exact O
  obtain ⟨k,kl,eq⟩ := List.getElem_of_mem (chart.cover (addr a i,0) rfl own)
  have idx : S.getD k fall=(addr a i,0) := (List.getElem_eq_getD (h:=kl) fall).symm.trans eq
  have b := chart.length
  have ne : k≠len := by
    intro E
    subst k
    have K := congrArg Prod.snd (chart.terminal.symm.trans idx)
    change (10 : Fin 11)=0 at K
    contradiction
  exact ⟨k,by omega,idx⟩

/-- A single concrete ISSUE8 capture picks one bank for every LS slot
of the original complete LOAD tour. For each source the resulting
frozen packet is the immutable old bank at that source's real K0
mark. No per-source launch witnesses or caller-supplied visit lists. -/
theorem common_original_bank {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam width : Nat) (strip : Strip B base a seam width)
    (rootAt : a=(S.getD 0 fall).1)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 8 (.back 0))) :
    ∃ (lead : List (Fin n)) (launch : Fin n) (suffix : List (Fin n)) (bank : Fin 3),
      w=lead++launch::suffix ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      bank.val=(captures.read ((play x lead) (S.getD 0 fall).1).long).toNat / 16 % 4 ∧
      let y := ring (play x lead) launch
      ∀ i, i<seam → (longGeometry B (base (addr a i))).inside=true →
        ∃ (pre : List (Fin n)) (rest : List (Fin n)) (k : Nat),
          suffix=pre++(addr a i)::rest ∧ k<len ∧ S.getD k fall=(addr a i,0) ∧
          Event hp (fun j=>S.getD j fall) len (play y pre) (addr a i)
            (.busy 8 (.out k)) (.busy 8 (.out (k+1))) ∧
          (readLane (Sheet.index .ls) (ring (play y pre) (addr a i) (addr a i)).long).frozen=
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
  have uw : u<64 := (captures.read old).isLt
  obtain ⟨bank,_,idxBank⟩ := captured_operand_index u uw valid false
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
  intro i hi inBase
  obtain ⟨k,kl,idx⟩ := ls_ord hp chart a seam width i strip rootAt hi
  obtain ⟨pre,e,rest,R,part,ev,after⟩ := busy_crosses hp T kl 0 rfl (Nat.zero_le _)
  let z := play y pre
  have cur := busy_end hp part
  have part' := busy_append hp part (.cons cur ev (.nil (busy_start hp after)))
  have trail' := busy_load_word hp chart sep part' u uw valid 0 (k+1) rfl rfl start
  have afterF := load_word_carries hp trail' u uw valid start
  rw [BStarResetSchedule.run_append] at afterF
  have q : project (fun j=>S.getD j fall) (ring z e) (k+1)=.forward (payload u) := afterF
  obtain ⟨cl,d,f,selected,dest,src,_⟩ := BStarNumericChronology.ring_departure
    hp chart e (sep e) 8 k kl cur.1 cur.2.1 cur.2.2 (payload u) q rfl
  have kc : cl.source.occurrence=0 := congrArg Prod.snd (src.symm.trans idx)
  have mem : cl∈orderedCommands (oldPair B z e) := by
    rw [←actualOffers_claims _ ((z e).long,(z (rightNeighbor e)).long)]
    exact List.mem_map.mpr ⟨_,selected,rfl⟩
  obtain ⟨srcL,nd⟩ := k0_link_left (oldPair B z e) cl d mem kc dest
  have loc := congrArg Prod.fst (src.symm.trans idx)
  have ee : e=addr a i := by rwa [srcL] at loc
  have inside : (longGeometry B (z e)).inside=true := by
    have same := congrArg (fun z : Bool × Bool × Bool => z.2.1) (cur.1.1 e)
    exact same.symm.trans (ee.symm ▸ inBase)
  have ownerRoot := (endpoint_spec (oldH6 B base) hh o 0).2.1
  rw [←chart.root,←rootAt] at ownerRoot
  have own : dataOwner (oldH6 B base) e .ls=o.val := by
    unfold dataOwner commandOwner at *
    rw [ee,ls_same_word hp strip hh i hi]
    exact ownerRoot
  have tr := busy_load_word hp chart sep part u uw valid 0 k rfl rfl start
  have Z : (root,0)=S.getD 0 fall := Prod.ext rfl root0.symm
  have loadWord : LoadWord hp y (root,0) pre (address e cl.source) := by
    rw [Z,←src]; exact tr
  obtain ⟨actualBank,bk,F⟩ := pointed_freeze_from_launch hp chart Launch pc8 pre e .left false cl
    (sep e) k loadWord cur src.symm own mem nd srcL inside
  have one : actualBank=bank := Fin.ext (bk.trans idxBank.symm)
  subst actualBank
  exact ⟨pre,rest,k,ee ▸ R,kl,idx,ee ▸ ev,ee ▸ F⟩

/-- Every source digit, and no source padding, is a LOAD target.
The whole source sector has length `seam`, not merely `width`. -/
theorem source_digit_chart {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (a : Fin n) (seam width : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (BStarH6Ordinal.oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤BStarH6Ordinal.oldOrdinal B base hh j+1) :
    width≤seam ∧ ∀ i<seam,
      BStarH6Ordinal.oldOrdinal B base hh (addr a i)=i ∧
      ((longGeometry B (base (addr a i))).inside=true ↔ i<width) ∧
      ∃ k<len,S.getD k fall=(addr a i,0) := by
  have H : addr a 0=a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
  have O : BStarH6Ordinal.oldOrdinal B base hh (addr a 0)=0 := by
    apply (BStarH6Ordinal.ordinal_zero _ hh _).mpr
    rw [H]
    exact strip.source_header
  have pos := strip.seam_pos
  have ordinal (i : Nat) (I : i<seam) : BStarH6Ordinal.oldOrdinal B base hh (addr a i)=i := by
    have E := BStarCopyRightStrip.address_ordinal_run a (oldH6 B base) hh 0 (seam-1)
      (by intro j J K; simpa only [Nat.zero_add] using strip.ls_body j J (by omega))
      i (by omega)
    change BStarH6Ordinal.oldOrdinal B base hh (addr a (0+i))=BStarH6Ordinal.oldOrdinal B base hh (addr a 0)+i at E
    simpa only [Nat.zero_add,O] using E
  have N : rightNeighbor (addr a (seam-1))=addr a seam := by
    rw [←BStarCopyRightStrip.addr_next,show seam-1+1=seam by omega]
  have W := notShort (addr a (seam-1)) (N.symm ▸ strip.dest_header)
  rw [ordinal _ (by omega),show seam-1+1=seam by omega] at W
  refine ⟨W,?_⟩
  intro i I
  exact ⟨ordinal i I,by rw [flags,ordinal i I,decide_eq_true_eq],ls_ord hp chart a seam width i strip root I⟩

#print axioms source_digit_chart
#print axioms common_original_bank
end L4.BStarCopyLeftOneCapture
