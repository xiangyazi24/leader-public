import Leader.L4.BStarNativeActualLoadAccepted
import Leader.L4.BStarCommitReceiptAuth

namespace L4.BStarNativeCommitHandoff
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor BStarLongLayout
open BStarLongCommand BStarLongEvents BStarLongClaims BStarCommitIssue
open BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarNativeActualLoadAccepted BStarCommitTailScan BStarCommitReceiptAuth
open BStarCommitGeneratedTail
open BStarH6WordChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The bank choice used by the actual publication is certified by
the actual selecting receipt on this very post-407 tail. -/
theorem selecting_receipt {base old x : X} {addr : Nat→Pos n} {len : Nat}
    {rem rest : List (Fin n)} {mark center : Fin n}
    (H : CommitHandoff hp base old x addr len rem rest mark center)
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e) :
    ∃ pre e post op f, rem=pre++e::post ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some H.descriptor ∧
      bind (longGeometry B (run x pre (addr 0).1)) 0
        (atSite (run x pre (addr 0).1).long 0)=.reply f ∧
      ReceiptBank op H.descriptor f H.bank := by
  let root := (addr 0).1
  have hlt : pc x root<411 := by have E : pc x root=408 := H.hit408; rw [E]; decide
  obtain ⟨pre,e,post,op,W,P,_,current,event,postPc,G⟩ :=
    first_411 hp K sep H.tail H.band hlt H.issue411
  have oldH : oldH6 B (run x pre) root=true := (H.band pre (e::post) W).1
  obtain ⟨d,D⟩ := selecting_has_descriptor hp K oldH (sep e) current event postPc
  have after : TailBand hp (step (run x pre) e) root post := by
    intro u v E
    have F : rem=(pre++e::u)++v := by rw [W,E,List.append_assoc]; rfl
    have J := H.band (pre++e::u) v F
    rw [BStarResetSchedule.run_append] at J
    exact J
  have foreign := ready_411_foreign hp K sep G after rfl rfl postPc
  have frame := BStarCommitChoiceHistory.foreign_word hp (step (run x pre) e) root post foreign
    (fun u a v E=>(after u (a::v) E).1)
  have join : run x rem=run (step (run x pre) e) post := by
    rw [W,BStarResetSchedule.run_append]
    rfl
  have result := selected_tail_result hp K oldH (sep e) current event d D (.inr (.inr postPc))
  obtain ⟨desc,f,reply,select⟩ := result
  have before := before_choice_bytes hp K P
  have descEnd : sourceDescriptor.read (run x rem root).long=
      sourceDescriptor.read (run x pre root).long := by
    rw [join]
    exact frame.1.trans desc
  have authDesc : BStarLongPublication.decode (sourceDescriptor.read (run x pre root).long)=some H.descriptor :=
    (congrArg BStarLongPublication.decode descEnd).symm.trans H.decoded
  have same : d=H.descriptor := Option.some.inj (D.symm.trans authDesc)
  subst d
  have Decode0 : BStarLongPublication.decode (sourceDescriptor.read (x root).long)=some H.descriptor :=
    (congrArg BStarLongPublication.decode before).symm.trans D
  refine ⟨pre,e,post,op,f,W,Decode0,reply,?_⟩
  have choiceEq (b : Fin 3)
      (E : choice.read (step (run x pre) e root).long=BitVec.ofNat 2 b.val) : H.bank=b := by
    have Q := frame.2.trans E
    rw [←join] at Q
    have V := congrArg BitVec.toNat Q
    change _=b.val%4 at V
    rw [H.choice,Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide : 3<4))] at V
    exact Fin.ext V
  rcases select postPc with ⟨o,n,k,L⟩|⟨o,n,L⟩
  · exact .inl ⟨o,n,k,choiceEq _ L⟩
  · exact .inr ⟨o,n,choiceEq _ L⟩

theorem actual_publication {base old x : X} {addr : Nat→Pos n} {len : Nat}
    {rem rest : List (Fin n)} {mark center : Fin n}
    (H : CommitHandoff hp base old x addr len rem rest mark center) :
    let g := oldPair B old mark
    let raw : Pair (BitVec LW) := ((old mark).long,(old (rightNeighbor mark)).long)
    (⟨.left,H.bank⟩ : Publication)∈(longTrace g raw).publications := by
  dsimp only
  obtain ⟨C,p,sel,lit,desc⟩ := H.selected
  let g := oldPair B old mark
  let raw : Pair (BitVec LW) := ((old mark).long,(old (rightNeighbor mark)).long)
  let P : Publication := ⟨C.source.side,H.bank⟩
  have mem : P∈(longTrace g raw).publications :=
    (literal_event_iff g raw P).mpr ⟨C,p,sel,rfl,lit⟩
  have E := literal_endpoint_left g raw P mem
  change C.source.side=.left at E
  simpa only [P,E] using mem

#print axioms selecting_receipt
#print axioms actual_publication
end L4.BStarNativeCommitHandoff
